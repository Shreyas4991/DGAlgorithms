import DGAlgorithms.Examples

unsafe def pp [Fintype V] (N : NonSimplePortNumbered V) (f : V → String) : String := Id.run <| do
  let mut result := ""
  let mut recorded : Finset (String × ℕ) := ∅

  for v in (Finset.univ : Finset V).1.unquot do
    let d := N.degree v
    let mut line := String.intercalate "|" do
      let i ← List.finRange d
      return s!"<p{i}>{f v},{(i : ℕ) + 1}"
    result := result.append s!"    {f v} [label=\"{line}\"];\n"

  for v in (Finset.univ : Finset V).1.unquot do
    let d := N.degree v
    for i in List.finRange d do
      if (f v, (i : ℕ)) ∈ recorded then continue
      let w := N.ofPort v i
      let j := N.reversePort v i
      recorded := insert (f w, (j : ℕ)) recorded
      if (f v, (i : ℕ)) = (f w, (j : ℕ)) then
        result := result.append s!"    {f v}:p{i} -- {f w}:p{j} [dir=forward];\n"
      else
        result := result.append s!"    {f v}:p{i} -- {f w}:p{j} [dir=both];\n"

  result := "graph {\n    rankdir = LR;\n    node [shape=record];\n" ++ result ++ "}\n"
  return result

unsafe def pp' [Fintype V] (N : NonSimplePortNumbered V) (f : V → String) : String := Id.run <| do
  let mut result := ""
  let mut recorded : Finset (String × ℕ) := ∅

  for v in (Finset.univ : Finset V).1.unquot do
    let d := N.degree v
    for i in List.finRange d do
      if (f v, (i : ℕ)) ∈ recorded then continue
      let w := N.ofPort v i
      let j := N.reversePort v i
      recorded := insert (f w, (j : ℕ)) recorded
      result := result.append s!"    {f v} -- {f w} [taillabel={i}, headlabel={j}, labelangle=0];\n"

  result := "graph {\n    node [shape=circle];\n" ++ result ++ "}\n"
  return result
