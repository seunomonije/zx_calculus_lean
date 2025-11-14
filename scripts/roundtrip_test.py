#!/usr/bin/env python3
"""
Roundtrip Test: PyZX → Lean → PyZX

Tests the full pipeline:
1. Create circuits in PyZX
2. Export to .qgraph
3. Load in Lean, parse to ZxTerm
4. Serialize back to .qgraph
5. Load back in PyZX
6. Check equivalence using PyZX tensor comparison
"""

import sys
import json
import subprocess
from pathlib import Path
from typing import Tuple, Optional
import tempfile

try:
    import pyzx as zx
except ImportError:
    print("Error: pyzx not installed. Install with: pip install pyzx")
    sys.exit(1)

# Color codes
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'


class RoundtripTester:
    """Test roundtrip conversion: PyZX → Lean → PyZX"""
    
    def __init__(self, lean_script: str = "scripts/RoundtripLean.lean"):
        self.lean_script = Path(lean_script)
        self.test_dir = Path(tempfile.mkdtemp(prefix="roundtrip_"))
        self.results = []
        
    def create_test_circuits(self):
        """Create a suite of test circuits"""
        circuits = {}
        
        # 1. Single Hadamard
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        circuits["hadamard"] = c
        
        # 2. Identity (just a wire)
        c = zx.Circuit(1)
        circuits["identity"] = c
        
        # 3. Z-phase gate
        c = zx.Circuit(1)
        c.add_gate("ZPhase", 0, 0.25)  # π/4
        circuits["z_phase"] = c
        
        # 4. X-phase gate
        c = zx.Circuit(1)
        c.add_gate("XPhase", 0, 0.5)  # π/2
        circuits["x_phase"] = c
        
        # 5. H ; Z composition
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        c.add_gate("ZPhase", 0, 0.5)
        circuits["h_z_comp"] = c
        
        # 6. Two qubits: H on first, Z on second
        c = zx.Circuit(2)
        c.add_gate("HAD", 0)
        c.add_gate("ZPhase", 1, 0.25)
        circuits["two_qubit_parallel"] = c
        
        # 7. CNOT (as ZX diagram)
        c = zx.Circuit(2)
        c.add_gate("CNOT", 0, 1)
        circuits["cnot"] = c
        
        # 8. Bell state preparation
        c = zx.Circuit(2)
        c.add_gate("HAD", 0)
        c.add_gate("CNOT", 0, 1)
        circuits["bell_state"] = c
        
        # 9. Three Hadamards in sequence
        c = zx.Circuit(1)
        c.add_gate("HAD", 0)
        c.add_gate("HAD", 0)
        c.add_gate("HAD", 0)
        circuits["three_hadamards"] = c
        
        # 10. Simple Z spider (2-ary)
        g = zx.Graph()
        v0 = g.add_vertex(0, 0, 0)  # Input boundary
        v1 = g.add_vertex(1, 1, 0)  # Z spider
        v2 = g.add_vertex(0, 2, 0)  # Output boundary
        g.add_edge((v0, v1))
        g.add_edge((v1, v2))
        g.set_inputs([v0])
        g.set_outputs([v2])
        circuits["simple_z_spider"] = g
        
        return circuits
    
    def export_pyzx_circuit(self, circuit, name: str) -> Path:
        """Export PyZX circuit/graph to .qgraph file"""
        if isinstance(circuit, zx.Circuit):
            g = circuit.to_graph()
        else:
            g = circuit
            
        filepath = self.test_dir / f"{name}_original.qgraph"
        
        # Use PyZX's native serialization
        with open(filepath, 'w') as f:
            f.write(g.to_json())
        
        return filepath
    
    def run_lean_roundtrip(self, input_file: Path, output_file: Path) -> Tuple[bool, str]:
        """
        Run Lean script to parse and serialize back.
        Returns (success, error_message)
        """
        try:
            # Use absolute path to lake
            lake_path = Path.home() / ".elan" / "bin" / "lake"
            result = subprocess.run(
                [str(lake_path), "env", "lean", "--run", str(self.lean_script), 
                 str(input_file), str(output_file)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=Path.cwd()  # Ensure we're in project root
            )
            
            if result.returncode != 0:
                return False, f"Lean failed: {result.stderr}"
            
            if not output_file.exists():
                return False, f"Output file not created: {output_file}"
            
            return True, ""
            
        except subprocess.TimeoutExpired:
            return False, "Lean script timed out"
        except Exception as e:
            return False, f"Exception: {str(e)}"
    
    def load_qgraph(self, filepath: Path) -> Optional[zx.Graph]:
        """Load .qgraph file into PyZX"""
        try:
            with open(filepath, 'r') as f:
                g = zx.Graph.from_json(f.read())
                # Auto-detect inputs/outputs from boundary vertices
                g.auto_detect_io()
                return g
        except Exception as e:
            print(f"  {RED}✗{RESET} Failed to load {filepath.name}: {e}")
            return None
    
    def compare_graphs(self, g1: zx.Graph, g2: zx.Graph, name: str) -> Tuple[bool, str]:
        """
        Compare two PyZX graphs for equivalence.
        Returns (equivalent, details)
        """
        try:
            # Basic structural checks (inputs() and outputs() are methods)
            if len(g1.inputs()) != len(g2.inputs()):
                return False, f"Input count mismatch: {len(g1.inputs())} vs {len(g2.inputs())}"
            
            if len(g1.outputs()) != len(g2.outputs()):
                return False, f"Output count mismatch: {len(g1.outputs())} vs {len(g2.outputs())}"
            
            # Compare tensor representations
            # This is the gold standard - checks if circuits are equivalent
            t1 = g1.to_tensor()
            t2 = g2.to_tensor()
            
            if not zx.compare_tensors(t1, t2, preserve_scalar=False):
                return False, "Tensor representations differ"
            
            return True, "Graphs are equivalent"
            
        except Exception as e:
            # If tensor comparison fails, try simpler checks
            return False, f"Comparison error: {str(e)}"
    
    def test_circuit(self, name: str, circuit) -> dict:
        """Test a single circuit through the roundtrip"""
        print(f"\n{BLUE}Testing:{RESET} {name}")
        print("  " + "─" * 60)
        
        result = {
            "name": name,
            "passed": False,
            "error": None,
            "details": {}
        }
        
        # Step 1: Export original from PyZX
        print(f"  {YELLOW}[1/4]{RESET} Exporting from PyZX...")
        original_file = self.export_pyzx_circuit(circuit, name)
        print(f"        → {original_file.name}")
        
        # Step 2: Run Lean roundtrip
        print(f"  {YELLOW}[2/4]{RESET} Running Lean roundtrip...")
        output_file = self.test_dir / f"{name}_roundtrip.qgraph"
        success, error = self.run_lean_roundtrip(original_file, output_file)
        
        if not success:
            result["error"] = error
            print(f"        {RED}✗{RESET} {error}")
            return result
        
        print(f"        → {output_file.name}")
        
        # Step 3: Load both graphs
        print(f"  {YELLOW}[3/4]{RESET} Loading graphs...")
        g_original = self.load_qgraph(original_file)
        g_roundtrip = self.load_qgraph(output_file)
        
        if g_original is None or g_roundtrip is None:
            result["error"] = "Failed to load graphs"
            return result
        
        result["details"]["original_vertices"] = len(g_original.vertices())
        result["details"]["original_edges"] = len(list(g_original.edges()))
        result["details"]["roundtrip_vertices"] = len(g_roundtrip.vertices())
        result["details"]["roundtrip_edges"] = len(list(g_roundtrip.edges()))
        
        print(f"        Original:  {result['details']['original_vertices']} vertices, "
              f"{result['details']['original_edges']} edges")
        print(f"        Roundtrip: {result['details']['roundtrip_vertices']} vertices, "
              f"{result['details']['roundtrip_edges']} edges")
        
        # Step 4: Compare equivalence
        print(f"  {YELLOW}[4/4]{RESET} Checking equivalence...")
        equivalent, details = self.compare_graphs(g_original, g_roundtrip, name)
        
        result["passed"] = equivalent
        result["details"]["comparison"] = details
        
        if equivalent:
            print(f"        {GREEN}✓{RESET} {details}")
        else:
            print(f"        {RED}✗{RESET} {details}")
            result["error"] = details
        
        return result
    
    def run_all_tests(self):
        """Run all roundtrip tests"""
        print(f"{BLUE}{'=' * 70}{RESET}")
        print(f"{BLUE}PyZX → Lean → PyZX Roundtrip Tests{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}")
        
        print(f"\nTest directory: {self.test_dir}")
        print(f"Lean script: {self.lean_script}")
        
        if not self.lean_script.exists():
            print(f"\n{RED}Error:{RESET} Lean script not found: {self.lean_script}")
            print("Creating it now...")
            self.create_lean_script()
        
        circuits = self.create_test_circuits()
        print(f"\nRunning {len(circuits)} tests...")
        
        for name, circuit in circuits.items():
            result = self.test_circuit(name, circuit)
            self.results.append(result)
        
        self.print_summary()
        
        return all(r["passed"] for r in self.results)
    
    def print_summary(self):
        """Print test summary"""
        print(f"\n{BLUE}{'=' * 70}{RESET}")
        print(f"{BLUE}Test Summary{RESET}")
        print(f"{BLUE}{'=' * 70}{RESET}\n")
        
        passed = sum(1 for r in self.results if r["passed"])
        failed = len(self.results) - passed
        
        print(f"Total:  {len(self.results)} tests")
        print(f"Passed: {GREEN}{passed}{RESET}")
        print(f"Failed: {RED}{failed}{RESET}")
        
        if failed > 0:
            print(f"\n{RED}Failed tests:{RESET}")
            for r in self.results:
                if not r["passed"]:
                    print(f"  • {r['name']}: {r['error']}")
        
        print(f"\n{BLUE}{'=' * 70}{RESET}")
        
        if failed == 0:
            print(f"{GREEN}✓ All roundtrip tests passed!{RESET}")
            print(f"{GREEN}The serializer is working correctly.{RESET}")
        else:
            print(f"{RED}✗ Some tests failed. Check details above.{RESET}")
        
        print(f"{BLUE}{'=' * 70}{RESET}\n")
    
    def create_lean_script(self):
        """Create the Lean roundtrip script if it doesn't exist"""
        content = """import ZxCalculus.Parser.QGraph

open ZxCalculus.Parser

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath, outputPath] =>
    try
      -- Parse input .qgraph file
      let qgraph ← parseQGraphFile ⟨inputPath⟩
      
      -- Attempt to reconstruct ZxTerm
      match reconstructZxTermSimple qgraph with
      | .error e =>
        IO.eprintln s!"Failed to reconstruct: {e}"
        return 1
      | .ok ⟨n, m, term⟩ =>
        -- Serialize back to .qgraph
        saveZxTermAsQGraph ⟨outputPath⟩ term
        return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: RoundtripLean <input.qgraph> <output.qgraph>"
    return 1
"""
        self.lean_script.parent.mkdir(parents=True, exist_ok=True)
        with open(self.lean_script, 'w') as f:
            f.write(content)
        print(f"Created {self.lean_script}")


def main():
    tester = RoundtripTester()
    success = tester.run_all_tests()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()

