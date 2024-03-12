import «CyclicFormulas»

open Std.Format Formula Program

def formula_in := dim (star (star (atom 1))) (prop 1)


def main : IO Unit := do
  -- let stdin  ← IO.getStdin
  let stdout ← IO.getStdout

  let φ := formula_in
  let Gφ := ToC2CF φ

  stdout.putStr <|
    s!"digraph \"{reprStr φ}\" \{"
    ++   "\n\tnode [shape=circle, fixedsize=true];"
    ++   "\n\tinit [label=\"\", shape=none]"
    ++ s!"\n\tinit -> {Gφ.vI}"

  forM (FinEnum.toList Gφ) fun v => stdout.putStr
    s!"\n\t{v} [color={Gφ.Ω v}, label=\"{Gφ.L v}\"]"

  forM (FinEnum.toList (Graph.edges Gφ)) fun ⟨(v, w), _⟩ => stdout.putStr
    s!"\n\t{v} -> {w}"

  stdout.putStrLn "\n}"