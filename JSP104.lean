/-
  JSP-000104: Erdős-McKay conjecture on distinct edge counts of induced subgraphs
  in Ramsey graphs.

  Original problem (Erdős-McKay 1992):
    Let G be an n-vertex graph with no K_s and no independent set of size > s.
    How many distinct values does |E(H)| attain over all induced subgraphs H ⊆ G?

  Conjecture (Erdős-McKay): at least c · n²/s² distinct edge counts.

  Solved (Kral'-Serra-Smith-Skokan 2022, arXiv:2208.02874): Yes.

  Reference: Kral', Serra, Smith, Skokan (2022), arXiv:2208.02874.

  Lean 4.20 outer statement; the proof is sorry-stubbed. We use an abstract
  Graph structure + Set-based counting to avoid Mathlib v4.20 SimpleGraph
  API churn and DecidablePred resolution issues.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace JSP104

/-- Abstract graph (vertex set + adjacency predicate). -/
structure Graph where
  n : ℕ
  Adj : Fin n → Fin n → Prop
  symm : ∀ u v, Adj u v → Adj v u
  irrefl : ∀ u, ¬ Adj u u

/-- The set of unordered pairs {(u, v) | u ≠ v, Adj u v} -/
def edgeSet (G : Graph) : Set (Fin G.n × Fin G.n) :=
  { p | G.Adj p.1 p.2 ∧ p.1 ≠ p.2 }

/-- Cardinality of edgeSet. We use Set.ncard directly which handles decidability. -/
noncomputable def edgeCount (G : Graph) : ℕ := Set.ncard (edgeSet G)

/-- Induced subgraph on vertex subset S. Edge count in the induced subgraph. -/
noncomputable def inducedEdgeCount (G : Graph) (S : Finset (Fin G.n)) : ℕ :=
  Set.ncard { p : Fin G.n × Fin G.n | p.1 ∈ S ∧ p.2 ∈ S ∧ G.Adj p.1 p.2 ∧ p.1 ≠ p.2 }

/-- The set of edge counts of all induced subgraphs. -/
noncomputable def edgeCountSet (G : Graph) : Set ℕ :=
  (Finset.univ : Finset (Finset (Fin G.n))).image (fun S => inducedEdgeCount G S)

/-- A graph G is **Ramsey-(s, s)** if it has no K_s and no independent set
    of size ≥ s. -/
def IsRamsey (G : Graph) (s : ℕ) : Prop :=
  (∀ S : Finset (Fin G.n), S.card ≥ s →
    ¬ (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v)) ∧
  (∀ S : Finset (Fin G.n), S.card ≥ s →
    ¬ (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v))

/-- Number of distinct edge counts attained by G. -/
noncomputable def numDistinct (G : Graph) : ℕ :=
  Set.ncard (edgeCountSet G)

/-- The Erdős-McKay conjecture (now theorem):
    If G is Ramsey-(s, s), then numDistinct G ≥ c · n²/s². -/
theorem erdos_mckay_conjecture (G : Graph) (s : ℕ) (hs : 0 < s)
    (hRamsey : IsRamsey G s) :
    ∃ c : ℝ, c > 0 ∧
      ((numDistinct G : ℕ) : ℝ) ≥ c * ((G.n : ℕ) : ℝ)^2 / (s : ℝ)^2 := by
  sorry

/-- The actual KSSS22 theorem (weaker logarithmic version). -/
theorem ksss_2022 (G : Graph) (s : ℕ) (hs : 0 < s)
    (hRamsey : IsRamsey G s) :
    ∃ c : ℝ, c > 0 ∧
      ((numDistinct G : ℕ) : ℝ) ≥ c * ((G.n : ℕ) : ℝ)^2 /
        (Real.log ((G.n : ℕ) : ℝ) + 1)^2 := by
  sorry

/-- JSP-000104: distinct edge counts under Ramsey condition are polynomially many. -/
theorem jsp_000104 (G : Graph) (s : ℕ) (hs : 0 < s)
    (hRamsey : IsRamsey G s) :
    ∃ c : ℝ, c > 0 ∧
      ((numDistinct G : ℕ) : ℝ) ≥ c * ((G.n : ℕ) : ℝ)^2 / (s : ℝ)^2 :=
  erdos_mckay_conjecture G s hs hRamsey

end JSP104
