import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularComponentCoverage
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_uniform_compact_prism_margin
    {E J : Type*} [TopologicalSpace E] [T2Space E] [Finite J]
    (A B : J → Set E) (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (hB : ∀ j, IsCompact (B j)) (Q : Set E) (hQ : IsCompact Q)
    (hends : ∀ j (y : B j), (y : E) ∈ Q →
      (0 : ℝ) < ((H j).symm y : E × ℝ).2 ∧ ((H j).symm y : E × ℝ).2 < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ δ ≤ 1/4 ∧ ∀ j (y : B j), (y : E) ∈ Q →
      δ ≤ ((H j).symm y : E × ℝ).2 ∧ ((H j).symm y : E × ℝ).2 ≤ 1-δ := by
  classical
  let height (j : J) (y : B j) : ℝ := ((H j).symm y : E × ℝ).2
  have hheight (j : J) : Continuous (height j) :=
    continuous_snd.comp (continuous_subtype_val.comp (H j).symm.continuous)
  let V := ⋃ j, height j '' {y : B j | (y : E) ∈ Q}
  have hcV : IsCompact V := by
    apply isCompact_iUnion
    intro j
    letI : CompactSpace (B j) := isCompact_iff_compactSpace.mp (hB j)
    exact ((hQ.isClosed.preimage continuous_subtype_val).isCompact).image (hheight j)
  have hV (t : ℝ) (ht : t ∈ V) : 0 < t ∧ t < 1 := by
    obtain ⟨j,y,hy,rfl⟩ := mem_iUnion.mp ht
    exact hends j y hy
  let T := V ∪ (fun t : ℝ => 1-t) '' V
  have hcT : IsCompact T := hcV.union (hcV.image (continuous_const.sub continuous_id))
  have hT (t : ℝ) (ht : t ∈ T) : 0 < t := by
    rcases ht with ht | ⟨u,hu,rfl⟩
    · exact (hV t ht).1
    · linarith [(hV u hu).2]
  by_cases hne : T.Nonempty
  · obtain ⟨a,ha,hmin⟩ := hcT.exists_isLeast hne
    let δ := min (a/2) (1/4 : ℝ)
    have ha0 := hT a ha
    refine ⟨δ,lt_min (by linarith) (by norm_num),lt_of_le_of_lt (min_le_right _ _) (by norm_num),
      min_le_right _ _,?_⟩
    intro j y hy
    have hyV : height j y ∈ V := mem_iUnion.mpr ⟨j,y,hy,rfl⟩
    have hlow := hmin (Or.inl hyV)
    have hhigh := hmin (Or.inr ⟨height j y,hyV,rfl⟩)
    have hδ : δ ≤ a/2 := min_le_left _ _
    change δ ≤ height j y ∧ height j y ≤ 1-δ
    constructor <;> linarith
  · refine ⟨1/4,by norm_num,by norm_num,le_rfl,?_⟩
    intro j y hy
    exact (hne ⟨height j y,Or.inl (mem_iUnion.mpr ⟨j,y,hy,rfl⟩)⟩).elim

theorem exists_original_compact_cut_prism_margin
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hzero : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (Q : Set E) (hQ : IsCompact Q) (hQS : Disjoint Q (g ⁻¹' S)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧ δ ≤ 1/4 ∧ ∀ j (y : F.ball j.1.1 j.1.2), (y : E) ∈ Q →
      δ ≤ ((H j).symm y : E × ℝ).2 ∧ ((H j).symm y : E × ℝ).2 ≤ 1-δ := by
  classical
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite (RegularOriginalCutCell K g S D F.BallIndex F.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  apply exists_uniform_compact_prism_margin
    (fun j => F.cut j.1.1 (i₀ j)) (fun j => F.ball j.1.1 j.1.2) H
    (fun j => (F.ball_pair j.1.1 j.1.2).isCompact) Q hQ
  intro j y hy
  have hyS : g y ∉ S := fun hs => disjoint_left.mp hQS hy hs
  have ht := ((H j).symm y).property.2
  have hnot (i : F.DiskIndex j.1.1) : (y : E) ∉ F.cut j.1.1 i := by
    intro hi
    exact hyS ((F.mem_cut_iff_physical hgi j.1.1
      (F.ball_subset_tetrahedron j.1.1 j.1.2 y.property)).mp (mem_iUnion.mpr ⟨i,hi⟩))
  have h0 : ((H j).symm y : E × ℝ).2 ≠ 0 := by
    intro he
    have hh := (hzero j ((H j).symm y)).mpr he
    exact hnot (i₀ j) (by simpa only [Homeomorph.apply_symm_apply] using hh)
  have h1 : ((H j).symm y : E × ℝ).2 ≠ 1 := by
    intro he
    have hh := (hone j ((H j).symm y)).mpr he
    exact hnot (i₁ j) (by simpa only [Homeomorph.apply_symm_apply] using hh)
  exact ⟨lt_of_le_of_ne ht.1 h0.symm,lt_of_le_of_ne ht.2 h1⟩

end PoincareConjecture.M76.PrismBelt
