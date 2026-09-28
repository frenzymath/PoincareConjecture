import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskPairCharts
import PoincareConjecture.Proofs.M76.Rigidity.RelativePairProduct

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

theorem exists_disk_parameter_product_of_pair_chart
    {X : Type*} [TopologicalSpace X] {R : Set X} {j : V2 → X}
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R) (H : OpenPartialHomeomorph X C3)
    (hmodel :
      (H.source ⊆ interior R ∧ ∀ x ∈ H.source, x ∈ j '' D ↔ (H x).2 = 0) ∨
      ((∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1) ∧
        ∀ x ∈ H.source, x ∈ j '' D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0))
    (z : D) (hzH : j z ∈ H.source) :
    ∃ q : OpenPartialHomeomorph (D × ℝ) R,
      (z, (0 : ℝ)) ∈ q.source ∧
      q.target ⊆ (Subtype.val : R → X) ⁻¹' H.source ∧
      (∀ s, (s, (0 : ℝ)) ∈ q.source → (q (s, 0) : X) = j s) ∧
      (∀ w ∈ q.source, (H (q w : X)).2 = w.2) ∧
      ∀ w ∈ q.source, (q w : X) ∈ j '' D ↔ w.2 = 0 := by
  let S : Set R := (Subtype.val : R → X) ⁻¹' (j '' D)
  let f : D → S := fun a => ⟨⟨j a, hDR a.property⟩, ⟨a, a.property, rfl⟩⟩
  have hf : Topology.IsEmbedding f := by
    have hval : Topology.IsEmbedding (fun y : S => ((y : R) : X)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hval.of_comp_iff.mp hemb
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := y.property
    exact ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext hay)⟩
  let b : D ≃ₜ S := hf.toHomeomorphOfSurjective hsurj
  have hb (a : D) : ((b a : R) : X) = j a := rfl
  have hbx : ((b z : R) : X) ∈ H.source := by rw [hb]; exact hzH
  obtain ⟨q0, hzq0, hq0H, hq00, hq0normal, hq0pair⟩ :
      ∃ q0 : OpenPartialHomeomorph (S × ℝ) R,
        (b z, (0 : ℝ)) ∈ q0.source ∧
        q0.target ⊆ (Subtype.val : R → X) ⁻¹' H.source ∧
        (∀ s, (s, (0 : ℝ)) ∈ q0.source → q0 (s, 0) = (s : R)) ∧
        (∀ w ∈ q0.source, (H (q0 w : X)).2 = w.2) ∧
        ∀ w ∈ q0.source, (q0 w : X) ∈ j '' D ↔ w.2 = 0 := by
    rcases hmodel with ⟨hinside, hplane⟩ | ⟨hregion, hhalfplane⟩
    · apply exists_relative_pair_product_with_normal H (univ : Set (ℝ × ℝ))
        ?_ ?_ (b z) hbx
      · intro x hx
        exact ⟨fun _ => mem_univ _, fun _ => interior_subset (hinside hx)⟩
      · intro x hx
        exact (hplane x hx).trans ⟨fun h => ⟨mem_univ _, h⟩, And.right⟩
    · exact exists_relative_pair_product_with_normal H {p : ℝ × ℝ | 0 ≤ p.1}
        hregion hhalfplane (b z) hbx
  let p := b.prodCongr (Homeomorph.refl ℝ)
  let q := p.toOpenPartialHomeomorph.trans q0
  refine ⟨q, ⟨mem_univ _, hzq0⟩, ?_, ?_, ?_, ?_⟩
  · exact fun y hy => hq0H hy.1
  · intro a ha
    change (q0 (b a, (0 : ℝ)) : X) = j a
    rw [hq00 (b a) ha.2]
    exact hb a
  · intro w hw
    exact hq0normal (p w) hw.2
  · intro w hw
    exact hq0pair (p w) hw.2

end PoincareConjecture.M76
