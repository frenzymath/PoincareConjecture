import PoincareConjecture.Proofs.M76.Mathlib.ConvexCylinderRadialMap
import PoincareConjecture.Proofs.M76.Mathlib.CompactImageSeparation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalPartition
import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isFinitePLBallPair_nested_convex_cylinderExterior
    (K : SimplicialComplex ℝ (E × ℝ)) (hK : K.faces.Finite)
    {Q C : Set E} (hQ : IsCompact Q) (hC : IsCompact C)
    (hQcv : Convex ℝ Q) (hCcv : Convex ℝ C)
    (hQ0 : (0 : E) ∈ interior Q) (hQC : Q ⊆ interior C)
    (hspace : K.space = frontier (C ×ˢ Icc (-1 : ℝ) 1))
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : Q = {x | ∀ i, L i x ≤ 1})
    (hdimEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsFinitePLBallPair F
      (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1})
      (frontier Q ×ˢ {(1 : ℝ)}) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let S := frontier (C ×ˢ Icc (-1 : ℝ) 1)
  let T := Q ×ˢ Icc (-1 : ℝ) 2
  let U := Q ×ˢ {(1 : ℝ)}
  let V := S \ interior Q ×ˢ {(1 : ℝ)}
  let P := frontier T ∩ {x | 1 ≤ x.2}
  let N := frontier T ∩ {x | x.2 ≤ 1}
  let R := frontier T ∩ {x | x.2 = 1}
  obtain ⟨f, e, hf, he, hef, hupper, hlower⟩ :=
    K.exists_finitePL_nested_cylinder_frontier_map hK hQ hC hQcv hCcv
      hQ0 hQC hspace L hL hrep
  have hUs : U ⊆ S := prod_singleton_one_subset_frontier_cylinder
    (hQC.trans interior_subset)
  have hVs : V ⊆ S := sdiff_subset
  have hclosure : closure (interior Q) = Q :=
    (hQcv.closure_interior_eq_closure_of_nonempty_interior ⟨0, hQ0⟩).trans
      hQ.isClosed.closure_eq
  have hUV : U ∪ V = S := by
    have h := top_face_union_cylinderExterior (U := interior Q) (D := C)
      (by rw [hclosure]; exact hQC.trans interior_subset)
    simpa only [hclosure] using h
  have hUVrim : U ∩ V = frontier Q ×ˢ {(1 : ℝ)} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨subset_closure hx.1.1, fun hi => hx.2.2 ⟨hi, hx.1.2⟩⟩, hx.1.2⟩
    · intro hx
      have hxU : x ∈ U := ⟨hQ.isClosed.frontier_subset hx.1, hx.2⟩
      exact ⟨hxU, hUs hxU, fun hi => hx.1.2 hi.1⟩
  have htarget (x : E × ℝ) (hx : x ∈ S) : f x ∈ frontier T :=
    hef ⟨x, hx⟩ ▸ (e ⟨x, hx⟩).property
  have hfinj : InjOn f S := by
    intro x hx y hy hxy
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
      Subtype.ext ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.injective heq)
  have hfS : f '' S = frontier T := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact htarget x hx
    · intro y hy
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hef x).symm.trans (congrArg Subtype.val hx)⟩
  have hfP : MapsTo f U P := fun x hx => ⟨htarget x (hUs hx), hupper hx⟩
  have hfN : MapsTo f V N := fun x hx => ⟨htarget x (hVs hx), hlower hx⟩
  let M := LinearMap.cylinderUnitForms L
  let H := Finset.univ.image
    (fun i : ι ⊕ Bool => (M i).toAffineMap - AffineMap.const ℝ (E × ℝ) 1)
  have hTH : T = {x | ∀ A ∈ H, A x ≤ 0} := by
    rw [show T = {x | ∀ i, M i x ≤ 1} from LinearMap.cylinderUnitForms_region L hrep]
    ext x
    constructor
    · intro hx A hA
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      change M i x - 1 ≤ 0
      exact sub_nonpos.mpr (hx i)
    · intro hx i
      have h := hx ((M i).toAffineMap - AffineMap.const ℝ (E × ℝ) 1)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      change M i x - 1 ≤ 0 at h
      exact sub_nonpos.mp h
  have hTc : IsCompact T := hQ.prod isCompact_Icc
  have hTcv : Convex ℝ T := hQcv.prod (convex_Icc _ _)
  obtain ⟨J, hJ, hJT⟩ := hTc.exists_finite_triangulation_of_halfspaces H hTH
  let A : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ E ℝ).toAffineMap - AffineMap.const ℝ (E × ℝ) 1
  have hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F + 1 := by
    simp only [Module.finrank_prod, Module.finrank_self, hdimEF]
  have hplane : ∃ w ∈ interior T, A w = 0 := by
    refine ⟨(0, 1), ?_, ?_⟩
    · rw [interior_prod_eq, interior_Icc]
      exact ⟨hQ0, by norm_num, by norm_num⟩
    · change (1 : ℝ) - 1 = 0
      ring
  have hP : IsFinitePLBallPair F P R := by
    have hneg : ∃ q ∈ interior T, A q < 0 := by
      refine ⟨(0, 0), ?_, ?_⟩
      · rw [interior_prod_eq, interior_Icc]
        exact ⟨hQ0, by norm_num, by norm_num⟩
      · change (0 : ℝ) - 1 < 0
        norm_num
    have h := J.isFinitePLBallPair_convex_frontier_affine_cap hJ hTc hTcv hJT A
      hneg hplane hdim
    change IsFinitePLBallPair F (frontier T ∩ {x | 0 ≤ x.2 - 1})
      (frontier T ∩ {x | x.2 - 1 = 0}) at h
    simpa only [sub_nonneg, sub_eq_zero] using h
  have hN : IsFinitePLBallPair F N R := by
    have hneg : ∃ q ∈ interior T, (-A) q < 0 := by
      refine ⟨(0, 3 / 2), ?_, ?_⟩
      · rw [interior_prod_eq, interior_Icc]
        exact ⟨hQ0, by norm_num, by norm_num⟩
      · change -((3 / 2 : ℝ) - 1) < 0
        norm_num
    have hplane' : ∃ w ∈ interior T, (-A) w = 0 := by
      obtain ⟨w, hw, hAw⟩ := hplane
      exact ⟨w, hw, by change -A w = 0; rw [hAw, neg_zero]⟩
    have h := J.isFinitePLBallPair_convex_frontier_affine_cap hJ hTc hTcv hJT (-A)
      hneg hplane' hdim
    change IsFinitePLBallPair F (frontier T ∩ {x | 0 ≤ -(x.2 - 1)})
      (frontier T ∩ {x | -(x.2 - 1) = 0}) at h
    simpa only [neg_nonneg, sub_nonpos, neg_eq_zero, sub_eq_zero] using h
  have hPN : P ∩ N = R := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.2.2 hx.1.2⟩
    · intro hx
      exact ⟨⟨hx.1, hx.2.ge⟩, ⟨hx.1, hx.2.le⟩⟩
  have hPdense : closure (P \ N) = P := by
    have hdiff : P \ N = P \ R := by
      rw [← hPN]
      ext x
      simp only [mem_sdiff, mem_inter_iff]
      tauto
    rw [hdiff]
    exact hP.closure_sdiff
  have hNdense : closure (N \ P) = N := by
    have hdiff : N \ P = N \ R := by
      rw [← hPN]
      ext x
      simp only [mem_sdiff, mem_inter_iff]
      tauto
    rw [hdiff]
    exact hN.closure_sdiff
  have hfU : f '' U = P := (hQ.prod isCompact_singleton).image_eq_of_dense_sdiff
    (hf.continuousOn.mono hUs) (by rw [hUV, hfS]; exact inter_subset_left)
    hfP hfN hPdense
  have hfV : f '' V = N := (isCompact_cylinderExterior hC isOpen_interior
    (interior_subset.trans hQC)).image_eq_of_dense_sdiff
      (hf.continuousOn.mono hVs)
      (by rw [union_comm V U, hUV, hfS]; exact inter_subset_left)
      hfN hfP hNdense
  have hpreU : S ∩ f ⁻¹' P = U := by
    rw [← hfU, inter_comm]
    exact hfinj.preimage_image_inter hUs
  have hpreV : S ∩ f ⁻¹' N = V := by
    rw [← hfV, inter_comm]
    exact hfinj.preimage_image_inter hVs
  have hpreR : S ∩ f ⁻¹' R = frontier Q ×ˢ {(1 : ℝ)} := by
    rw [← hUVrim, ← hpreU, ← hpreV, ← hPN]
    ext x
    simp only [mem_inter_iff, mem_preimage]
    tauto
  have h := he.preimage_ballPair hN (show N ⊆ frontier T from inter_subset_left) hef
  change IsFinitePLBallPair F (S ∩ f ⁻¹' N) (S ∩ f ⁻¹' R) at h
  rwa [hpreV, hpreR] at h

end Geometry.SimplicialComplex
