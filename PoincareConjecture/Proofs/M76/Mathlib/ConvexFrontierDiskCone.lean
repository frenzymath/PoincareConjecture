import PoincareConjecture.Proofs.M76.Mathlib.RadialConeBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.convexJoin_zero_of_subset_frontier
    {d q C : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C) (hdC : d ⊆ frontier C) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {0} d)
      (d ∪ convexJoin ℝ {0} q) := by
  classical
  obtain ⟨e, he, heb⟩ := hd.exists_homeomorph AlexanderBaseConeModel.isFinitePLBallPair_top
  have hdne : d.Nonempty := hd.sdiff_nonempty.mono sdiff_subset
  have hqne : q.Nonempty := by
    obtain ⟨z, hz⟩ := AlexanderBaseConeModel.rim_nonempty
    let w : AlexanderBaseConeModel.top :=
      ⟨z, AlexanderBaseConeModel.isFinitePLBallPair_top.1 hz⟩
    refine ⟨e.symm w, (heb (e.symm w)).mpr ?_⟩
    simpa only [e.apply_symm_apply] using hz
  obtain ⟨f, ⟨K, hK, hKs, hf⟩, hef⟩ := he
  have hinj : InjOn f K.space := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hKs ▸ hx⟩ = e ⟨y, hKs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  let T := hf.embeddedImage hinj
  have hTs : T.space = AlexanderBaseConeModel.top := by
    rw [hf.embeddedImage_space, hKs]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hlinK := K.linearIndependent_faces_of_space_subset_frontier hcv hzero
    (hKs.subset.trans hdC)
  have hradK : InjOn (NormedSpace.normalize : E → E) K.space :=
    (hcv.injOn_normalize_frontier hzero).mono (hKs.subset.trans hdC)
  let M := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hM (z : (ℝ × ℝ) × ℝ) (hz : z ∈ AlexanderBaseConeModel.top) : M z = 1 :=
    AlexanderBaseConeModel.height_top z hz
  have hMT (z : (ℝ × ℝ) × ℝ) (hz : z ∈ T.space) : M z = 1 :=
    hM z (hTs.subset hz)
  have hlinT := T.linearIndependent_faces_of_linear_level M one_ne_zero hMT
  have hradT := M.injOn_normalize_of_level one_ne_zero hMT
  have hconeK : (K.coneAtZero hlinK hradK).space = convexJoin ℝ {0} d := by
    rw [K.coneAtZero_space_eq_convexJoin hlinK hradK (hKs.symm ▸ hdne), hKs]
  have htopne : T.space.Nonempty := hTs.symm ▸
    AlexanderBaseConeModel.isFinitePLBallPair_top.sdiff_nonempty.mono sdiff_subset
  have hconeT : (T.coneAtZero hlinT hradT).space =
      convexJoin ℝ {0} AlexanderBaseConeModel.top := by
    rw [T.coneAtZero_space_eq_convexJoin hlinT hradT htopne, hTs]
  obtain ⟨g, H, hg, hg0, hbase, hH⟩ := hf.exists_cone_extension_affine
    hinj hK hlinK hradK hlinT hradT
  have hHPL : H.IsFinitePL :=
    ⟨g, hg.finitePiecewiseAffineOn
      (SimplicialComplex.finite_coneAtZero_faces hK hlinK hradK), hH⟩
  let G := (Homeomorph.setCongr hconeK.symm).trans
    (H.trans (Homeomorph.setCongr hconeT))
  have hbd : d ∪ convexJoin ℝ {0} q ⊆ convexJoin ℝ {0} d :=
    union_subset (subset_convexJoin_right (singleton_nonempty (0 : E)))
      (convexJoin_mono_right hd.1)
  apply AlexanderBaseConeModel.isFinitePLBallPair_cone.of_homeomorph
    hbd G (hHPL.setCongr hconeK hconeT)
  intro x
  obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff d _).mp x.property
  have hval : (G x : (ℝ × ℝ) × ℝ) = r • (e ⟨y, hy⟩ : (ℝ × ℝ) × ℝ) := by
    change (H ⟨x, hconeK.symm ▸ x.property⟩ : (ℝ × ℝ) × ℝ) = _
    rw [hH, hxy, hg.cone_extension_smul hg0 hbase (hKs.symm ▸ hy) hr, hef ⟨y, hy⟩]
  have hd0 : (0 : E) ∉ d := fun h => (hdC h).2 hzero
  have hradd : InjOn (NormedSpace.normalize : E → E) d :=
    (hcv.injOn_normalize_frontier hzero).mono hdC
  rw [hval, hxy, mem_base_union_convexJoin_iff_of_radial hd.1 hqne hd0 hradd hy hr,
    M.mem_base_union_convexJoin_iff AlexanderBaseConeModel.isFinitePLBallPair_top.1
      AlexanderBaseConeModel.rim_nonempty hM (e ⟨y, hy⟩).property hr,
    heb ⟨y, hy⟩]

end Set
