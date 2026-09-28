import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ContractibleRetraction
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspacePunctureContractible
import PoincareConjecture.Proofs.M76.Mathlib.InteriorConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import Mathlib.Analysis.Normed.Affine.AddTorsor










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem contractibleSpace_faceLink_singleton_of_halfspace_patch
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices)
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hzero : ell p = 0) (hhalf : K.space ⊆ {z | 0 ≤ ell z})
    {V : Set E} (hV : IsOpen V) (hpV : p ∈ V)
    (hpatch : V ∩ {z | 0 ≤ ell z} ⊆ K.space) :
    ContractibleSpace (K.faceLink {p}).space := by
  let pK : K.space := ⟨p, K.vertices_subset_space hp⟩
  have hstar : (K.closedFaceStar {p}).space ∈ 𝓝[K.space] p := by
    rw [← map_nhds_subtype_val pK]
    apply K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hp pK
    simp [pK, intrinsicInterior_singleton]
  obtain ⟨η, hη, hηstar⟩ := Metric.mem_nhdsWithin_iff.mp hstar
  have hsmall : V ∩ Metric.ball p η ∈ 𝓝 p :=
    inter_mem (hV.mem_nhds hpV) (Metric.ball_mem_nhds p hη)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hballstar : Metric.ball p ε ∩ {z | 0 ≤ ell z} ⊆
      (K.closedFaceStar {p}).space := by
    intro z hz
    exact hηstar ⟨(hball hz.1).2, hpatch ⟨(hball hz.1).1, hz.2⟩⟩
  let B : Set E := (Metric.ball p ε ∩ {z | 0 ≤ ell z}) \ {p}
  let D : Set E := (K.closedFaceStar {p}).space \
    (affineSpan ℝ (({p} : Finset E) : Set E) : Set E)
  have hspan : (affineSpan ℝ (({p} : Finset E) : Set E) : Set E) = {p} := by
    simp only [Finset.coe_singleton, AffineSubspace.coe_affineSpan_singleton]
  have hBD : B ⊆ D := by
    intro z hz
    exact ⟨hballstar hz.1, hspan.symm ▸ hz.2⟩
  obtain ⟨R, hRcont, hRmap, hRline⟩ := K.exists_continuous_faceLink_retraction hK {p}
  have hpHull : p ∈ convexHull ℝ (({p} : Finset E) : Set E) := by simp
  have hcompact : IsCompact (K.faceLink {p}).space :=
    (K.faceLink {p}).isCompact_space_of_finite (finite_faceLink_faces hK {p})
  obtain ⟨M, hM, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 p
  let δ : ℝ := min (1 / 2) (ε / (2 * M))
  have hδpos : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδM : δ * M < ε := by
    have hle : δ ≤ ε / (2 * M) := min_le_right _ _
    have hle' : δ * (2 * M) ≤ ε := (le_div_iff₀ (by positivity)).mp hle
    nlinarith
  have hline (y : E) (hy : y ∈ (K.faceLink {p}).space) :
      AffineMap.lineMap p y δ ∈ B := by
    obtain ⟨hD, _⟩ := hRline p hpHull y hy δ ⟨hδpos, hδone⟩
    have hstarle : K.closedFaceStar {p} ≤ K := fun _ ht => ht.1
    refine ⟨⟨?_, hhalf (space_subset_of_le hstarle hD.1)⟩, ?_⟩
    · rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs,
        abs_of_pos hδpos, dist_comm]
      exact (mul_lt_mul_of_pos_left (Metric.mem_ball.mp (hbound hy)) hδpos).trans hδM
    · exact hspan ▸ hD.2
  let ρ : C(B, (K.faceLink {p}).space) :=
    ⟨fun z => ⟨R z, hRmap (hBD z.property)⟩,
      (hRcont.mono hBD).domRestrict.subtype_mk _⟩
  let σ : C((K.faceLink {p}).space, B) :=
    ⟨fun y => ⟨AffineMap.lineMap p (y : E) δ, hline y y.property⟩, by
      apply Continuous.subtype_mk
      simp only [AffineMap.lineMap_apply_module]
      exact continuous_const.add (continuous_const.smul continuous_subtype_val)⟩
  have hinverse : Function.LeftInverse ρ σ := by
    intro y
    apply Subtype.ext
    exact (hRline p hpHull y y.property δ ⟨hδpos, hδone⟩).2
  let : ContractibleSpace B :=
    ell.contractibleSpace_halfspace_punctured_ball hell hzero hε
  exact ρ.contractibleSpace_of_retract σ hinverse

end Geometry.SimplicialComplex
