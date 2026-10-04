import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.CollarTransitionAdjustment
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Aligning two actual collar patches

The transition is the literal composite of the two open charts. Its
compactly supported correction retains the incoming chart's whole
source, target, and base values, and produces an open agreement region.
See Brown1962, Lemma3, pp335--336 and Brown derivation008.
-/

set_option autoImplicit false

open Set

namespace BrownCollar

variable {B X : Type*} [MetricSpace B] [LocallyCompactSpace B] [TopologicalSpace X]

/-- Correct the second of two actual collar patches so that they
agree near a prescribed compact common base patch. Source and target
are retained as exact sets. See Brown1962, Lemma3 and derivation008. -/
theorem exists_collar_patch_alignment
    (c1 c2 : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X) (i : B → X)
    {K : Set B} (hK : IsCompact K)
    (hK1 : ∀ b ∈ K, collarBase b ∈ c1.source)
    (hK2 : ∀ b ∈ K, collarBase b ∈ c2.source)
    (hbase1 : ∀ b, collarBase b ∈ c1.source → c1 (collarBase b) = i b)
    (hbase2 : ∀ b, collarBase b ∈ c2.source → c2 (collarBase b) = i b) :
    ∃ d : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X,
      d.source = c2.source ∧ d.target = c2.target ∧
      (∀ b, collarBase b ∈ d.source → d (collarBase b) = i b) ∧
      ∃ V, IsOpen V ∧ collarBase '' K ⊆ V ∧
        V ⊆ c1.source ∩ d.source ∧ EqOn c1 d V := by
  let e := c2.trans c1.symm
  let W := collarBase ⁻¹' c1.source ∩ collarBase ⁻¹' c2.source
  have hbcont : Continuous (collarBase : B → B × Ico (0 : ℝ) 1) :=
    continuous_id.prodMk continuous_const
  have hW : IsOpen W := (c1.open_source.preimage hbcont).inter
    (c2.open_source.preimage hbcont)
  have hKW : K ⊆ W := fun b hb => ⟨hK1 b hb, hK2 b hb⟩
  have hsource (b : B) (hb : b ∈ W) : collarBase b ∈ e.source := by
    refine ⟨hb.2, ?_⟩
    change c2 (collarBase b) ∈ c1.target
    rw [hbase2 b hb.2, ← hbase1 b hb.1]
    exact c1.map_source hb.1
  have hfixed (b : B) (hb : b ∈ W) : e (collarBase b) = collarBase b := by
    change c1.symm (c2 (collarBase b)) = collarBase b
    rw [hbase2 b hb.2, ← hbase1 b hb.1]
    exact c1.left_inv hb.1
  obtain ⟨N, _, _, hNSW, H, _, hHbase, hpres, V, hV, hKV, hVN, hagree⟩ :=
    exists_transition_adjustment e hW hK hKW hsource hfixed
  have hNE : N ⊆ e.source := hNSW.trans inter_subset_left
  have hN2 : N ⊆ c2.source := fun _ hz => (hNE hz).1
  let d := H.transOpenPartialHomeomorph c2
  have hdS : d.source = c2.source := hpres c2.source hN2
  have hHE {z : B × Ico (0 : ℝ) 1} (hz : z ∈ V) : H z ∈ e.source := by
    have hzE : z ∈ e.source := hNE (hVN hz)
    have hp := hpres e.source hNE
    change z ∈ H ⁻¹' e.source
    rw [hp]
    exact hzE
  have hV1 : V ⊆ c1.source := by
    intro z hz
    have hz1 : e (H z) ∈ c1.source := (e.map_source (hHE hz)).1
    rwa [hagree z hz] at hz1
  refine ⟨d, hdS, rfl, ?_, V, hV, hKV, ?_, ?_⟩
  · intro b hb
    change c2 (H (collarBase b)) = i b
    rw [hHbase b]
    exact hbase2 b (hdS ▸ hb)
  · intro z hz
    exact ⟨hV1 hz, hdS.symm ▸ hN2 (hVN hz)⟩
  · intro z hz
    change c1 z = c2 (H z)
    calc
      c1 z = c1 (e (H z)) := congrArg c1 (hagree z hz).symm
      _ = c2 (H z) := c1.right_inv (hHE hz).2

end BrownCollar
