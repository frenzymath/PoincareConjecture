import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskNormalUnits
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedConstantNeighborhood
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.NormalProductAgreement










set_option autoImplicit false

open Set Metric Geometry SignType

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1




theorem exists_original_proper_disk_normal_labels
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q) :
    ∃ (E : D → OpenPartialHomeomorph X C3) (w : D → ℝ),
      (∀ z,
        j z ∈ (E z).source ∧ E z (j z) = 0 ∧
        (∀ i,
          LocallyPiecewiseAffineOn ((e i).symm.trans (E z)) ((e i).symm.trans (E z)).source ∧
          LocallyPiecewiseAffineOn ((E z).symm.trans (e i)) ((E z).symm.trans (e i)).source) ∧
        (((E z).source ⊆ interior R ∧
          ∀ x ∈ (E z).source, x ∈ j '' D ↔ (E z x).2 = 0) ∨
         ((∀ x ∈ (E z).source, x ∈ R ↔ 0 ≤ (E z x).1.1) ∧
          ∀ x ∈ (E z).source, x ∈ j '' D ↔ 0 ≤ (E z x).1.1 ∧ (E z x).2 = 0)) ∧
        w z ≠ 0) ∧
      ∀ i k (z : D), j z ∈ (E i).source ∩ (E k).source →
        ∃ V : Set R, IsOpen V ∧ (⟨j z, hDR z.property⟩ : R) ∈ V ∧
          MapsTo (Subtype.val : R → X) V ((E i).source ∩ (E k).source) ∧
          EqOn (fun y : R => sign (w i * (E i (y : X)).2))
            (fun y : R => sign (w k * (E k (y : X)).2)) V := by
  classical
  obtain ⟨H, q, a, hH, hac, ha⟩ :=
    exists_original_proper_disk_normal_units he hj hemb hDR hproper
  let B (i : D) : Set D := {z | (z, (0 : ℝ)) ∈ (q i).source}
  have hB (i : D) : IsOpen (B i) :=
    (q i).open_source.preimage (continuous_id.prodMk continuous_const)
  have hchoose (i : D) : ∃ O : Set X,
      IsOpen O ∧ j i ∈ O ∧ O ⊆ (H i).source ∧
      ∀ z : D, j z ∈ O → z ∈ B i ∧ a i z = a i i := by
    obtain ⟨hpoint, _, _, _, _, hqpoint, _, _, _, _⟩ := hH i
    exact hemb.exists_open_constant_neighborhood (hB i) (hac i)
      hqpoint (H i).open_source hpoint
  choose O hO hiO hOH hconst using hchoose
  let E (i : D) := (H i).restr (O i)
  let w (i : D) := BrownCollar.normalScalar (a i i)
  have hsource (i : D) : (E i).source = O i := by
    change ((H i).restr (O i)).source = O i
    rw [(H i).restr_source' _ (hO i)]
    exact inter_eq_right.mpr (hOH i)
  have hEsub (i : D) : (E i).source ⊆ (H i).source := by
    rw [hsource]
    exact hOH i
  refine ⟨E, w, ?_, ?_⟩
  · intro z
    obtain ⟨_, _, hzero, hcompat, hmodel, _, _, _, _, _⟩ := hH z
    refine ⟨?_, hzero, ?_, ?_, BrownCollar.normalScalar_ne_zero (a z z)⟩
    · rw [hsource]
      exact hiO z
    · intro i
      constructor
      · change LocallyPiecewiseAffineOn ((e i).symm.trans (H z)) _
        exact (hcompat i).1.mono ((e i).symm.trans (E z)).open_source
          (fun _ hv => ⟨hv.1, hEsub z hv.2⟩)
      · change LocallyPiecewiseAffineOn ((H z).symm.trans (e i)) _
        exact (hcompat i).2.mono ((E z).symm.trans (e i)).open_source
          (fun _ hv => ⟨hv.1.1, hv.2⟩)
    · rcases hmodel with hi | hb
      · exact Or.inl ⟨fun _ hx => hi.1 (hEsub z hx),
          fun x hx => hi.2 x (hEsub z hx)⟩
      · exact Or.inr ⟨fun x hx => hb.1 x (hEsub z hx),
          fun x hx => hb.2 x (hEsub z hx)⟩
  · intro i k z hz
    have hzi : z ∈ B i ∧ a i z = a i i :=
      hconst i z (by simpa only [hsource] using hz.1)
    have hzk : z ∈ B k ∧ a k z = a k k :=
      hconst k z (by simpa only [hsource] using hz.2)
    have hs := ha i k z hzi.1 hzk.1
    rw [hzi.2, hzk.2] at hs
    obtain ⟨_, _, _, _, _, _, _, hzeroi, hnormi, _⟩ := hH i
    obtain ⟨_, _, _, _, _, _, _, _, hnormk, _⟩ := hH k
    obtain ⟨V, hV, hzV, _, hsign⟩ := hs.exists_open_product_agreement
      (fun y : R => (H i (y : X)).2) (fun y : R => (H k (y : X)).2)
      hnormi hnormk
    have hbase : q i (z, 0) = (⟨j z, hDR z.property⟩ : R) :=
      Subtype.ext (hzeroi z hzi.1)
    rw [hbase] at hzV
    refine ⟨V ∩ (Subtype.val : R → X) ⁻¹' ((E i).source ∩ (E k).source),
      hV.inter (((E i).open_source.inter (E k).open_source).preimage
        continuous_subtype_val), ⟨hzV, hz⟩, fun _ hy => hy.2, ?_⟩
    intro y hy
    exact hsign hy.1

end PoincareConjecture.M76
