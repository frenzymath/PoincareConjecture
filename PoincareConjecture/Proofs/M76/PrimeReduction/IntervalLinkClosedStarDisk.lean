import PoincareConjecture.Proofs.M76.PrimeReduction.IntervalConeModel
import PoincareConjecture.Proofs.M76.Mathlib.LinearIndependentFaceRefinement
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

open PoincareConjecture.M76.PrimeReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem isFinitePLBallPair_closedStar_zero_of_interval
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) {a b : E}
    (hI : IsFinitePLBallPair ℝ (K.link 0).space {a, b}) :
    IsFinitePLBallPair (ℝ × ℝ) (K.closedStar 0).space
      ((K.link 0).space ∪ convexJoin ℝ {0} {a, b}) := by
  classical
  obtain ⟨e, he, heb⟩ := hI.exists_homeomorph IntervalCone.isFinitePLBallPair_base
  have hne : (K.link 0).space.Nonempty := ⟨a, hI.1 (by simp)⟩
  obtain ⟨f, ⟨J, hJ, hJs, hf⟩, hef⟩ := he
  obtain ⟨R, hR, hRJ, hRK⟩ := J.exists_finite_refinement_of_space_subset
    (K.link 0) hJ (finite_link_faces hK 0) hJs.subset
  have hRs : R.space = (K.link 0).space := hRJ.space_eq.trans hJs
  have hfR := hRJ.affineOnFaces hf
  have hinj : InjOn f R.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hRs ▸ hx⟩ = e ⟨y, hRs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let L := hfR.embeddedImage hinj
  have hLs : L.space = IntervalCone.base := by
    rw [hfR.embeddedImage_space, hRs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinR := R.linearIndependent_faces_of_face_containment (K.link 0)
    (fun _ hs => linearIndependent_of_mem_link_zero hs) hRK
  have hradR : InjOn (NormedSpace.normalize : E → E) R.space :=
    hRs.symm ▸ K.injOn_normalize_link
  let M := LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ
  have hM (x : ℝ × ℝ) (hx : x ∈ IntervalCone.base) : M x = 1 :=
    IntervalCone.level_base hx
  have hML (x : ℝ × ℝ) (hx : x ∈ L.space) : M x = 1 := hM x (hLs.subset hx)
  have hlinL := L.linearIndependent_faces_of_linear_level M one_ne_zero hML
  have hradL := M.injOn_normalize_of_level one_ne_zero hML
  have hstar : (K.closedStar 0).space = convexJoin ℝ {0} (K.link 0).space := by
    rw [← coneAtZero_link_eq_closedStar K hzero]
    exact (K.link 0).coneAtZero_space_eq_convexJoin _ _ hne
  have hconeR : (R.coneAtZero hlinR hradR).space = (K.closedStar 0).space := by
    rw [R.coneAtZero_space_eq_convexJoin hlinR hradR (hRs.symm ▸ hne), hRs, hstar]
  have hneL : L.space.Nonempty :=
    ⟨(1, 0), hLs.symm.subset (IntervalCone.isFinitePLBallPair_base.1 (by simp))⟩
  have hconeL : (L.coneAtZero hlinL hradL).space = convexJoin ℝ {0} IntervalCone.base := by
    rw [L.coneAtZero_space_eq_convexJoin hlinL hradL hneL, hLs]
  obtain ⟨g, H, hg, hg0, hbase, hH⟩ :=
    hfR.exists_cone_extension_affine hinj hR hlinR hradR hlinL hradL
  have hHPL : H.IsFinitePL :=
    ⟨g, hg.finitePiecewiseAffineOn (finite_coneAtZero_faces hR hlinR hradR), hH⟩
  let G := (Homeomorph.setCongr hconeR.symm).trans
    (H.trans (Homeomorph.setCongr hconeL))
  have hbd : (K.link 0).space ∪ convexJoin ℝ {0} {a, b} ⊆ (K.closedStar 0).space := by
    rw [hstar]
    exact union_subset (subset_convexJoin_right (singleton_nonempty (0 : E)))
      (convexJoin_mono_right hI.1)
  apply IntervalCone.isFinitePLBallPair_cone.of_homeomorph
    hbd G (hHPL.setCongr hconeR hconeL)
  intro x
  obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff (K.link 0).space _).mp
    (hstar.subset x.property)
  have hval : (G x : ℝ × ℝ) = r • (e ⟨y, hy⟩ : ℝ × ℝ) := by
    change (H ⟨x, hconeR.symm ▸ x.property⟩ : ℝ × ℝ) = _
    rw [hH, hxy, hg.cone_extension_smul hg0 hbase (hRs.symm ▸ hy) hr, hef ⟨y, hy⟩]
  have hb0 : (0 : ℝ × ℝ) ∉ IntervalCone.base := by
    intro hz
    have h := hM 0 hz
    exact zero_ne_one (by simpa only [map_zero] using h)
  rw [hval, hxy,
    mem_base_union_convexJoin_iff_of_radial hI.1 (by simp) K.zero_notMem_link_space
      K.injOn_normalize_link hy hr,
    mem_base_union_convexJoin_iff_of_radial IntervalCone.isFinitePLBallPair_base.1
      (by simp) hb0 (M.injOn_normalize_of_level one_ne_zero hM) (e ⟨y, hy⟩).property hr,
    heb ⟨y, hy⟩]

end Geometry.SimplicialComplex
