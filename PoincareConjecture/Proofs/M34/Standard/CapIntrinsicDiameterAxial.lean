import PoincareConjecture.Proofs.M34.Standard.NeckHeightControl
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceAxialMap

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem roundCylinderMetric_axial_le (f : ℝ → ℝ) (z : RoundCylinderSpace)
    (hf : DifferentiableAt ℝ f z.2) (hbound : |deriv f z.2| ≤ 1)
    (v : RoundCylinderTangent z) :
    EvolvingRoundCylinderMetric 0 (z.1, f z.2)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ))
          (fun w : RoundCylinderSpace => (w.1, f w.2)) z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ))
          (fun w : RoundCylinderSpace => (w.1, f w.2)) z v) ≤
      EvolvingRoundCylinderMetric 0 z v v := by
  have hs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ)
      (fun w : RoundCylinderSpace => f w.2) z :=
    hf.mdifferentiableAt.comp z mdifferentiableAt_snd
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ))
      (fun w : RoundCylinderSpace => (w.1, f w.2)) z v =
        (v.1, deriv f z.2 * v.2) := by
    rw [mfderiv_prodMk mdifferentiableAt_fst hs, mfderiv_fst]
    change (v.1, mfderiv ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) (f ∘ Prod.snd) z v) = _
    rw [mfderiv_comp_apply z hf.mdifferentiableAt mdifferentiableAt_snd v,
      mfderiv_snd, mfderiv_eq_fderiv]
    change (v.1, fderiv ℝ f z.2 v.2) = _
    rw [fderiv_eq_deriv_mul]
  rw [hd]
  have hsquare : (deriv f z.2) ^ 2 ≤ 1 := by
    nlinarith [(abs_le.mp hbound).1, (abs_le.mp hbound).2]
  have hproduct := mul_le_mul_of_nonneg_right hsquare (sq_nonneg v.2)
  dsimp [EvolvingRoundCylinderMetric]
  nlinarith

end PoincareConjecture.M34

namespace PoincareConjecture.CapCertificate

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem axialMap_tangentNorm_le_two {f : ℝ → ℝ} {c : ℝ}
    (hc : -N.epsilon⁻¹ < c) (hc' : c < N.epsilon⁻¹)
    (hf : ContDiff ℝ ∞ f) (hfix : ∀ s ≤ c, f s = s)
    (hderiv : ∀ s, |deriv f s| ≤ 1)
    (hvalid : ∀ x ∈ N.end_neck.carrier,
      f (N.end_neck.coordinate_inverse x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    g.tangentNorm (N.axialMap f x) (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v) ≤
      2 * g.tangentNorm x v := by
  by_cases he : x ∈ N.end_neck.carrier
  · let z := N.end_neck.coordinate_inverse x
    let E : RoundCylinderSpace → RoundCylinderSpace := fun w => (w.1, f w.2)
    let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ)) N.end_neck.coordinate_inverse x v
    let u := mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) E z w
    have hz := (N.end_neck.coordinate_inverse_mem x he).2
    have hzE : (E z).2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
      simpa only [E, z, N.end_neck_epsilon] using hvalid x he
    have hi := ((N.end_neck.coordinate_inverse_smooth x he).contMDiffAt
      (N.end_neck.carrier_open.mem_nhds he)).mdifferentiableAt (by simp)
    have hE : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)) E z :=
      mdifferentiableAt_fst.prodMk
        ((hf.differentiable (by simp) z.2).mdifferentiableAt.comp z mdifferentiableAt_snd)
    have hm := ((N.end_neck.coordinate_map_smooth (E z) ⟨mem_univ _, hzE⟩).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzE⟩)).mdifferentiableAt (by simp)
    have hlocal : N.axialMap f =ᶠ[𝓝 x]
        N.end_neck.coordinate_map ∘ (E ∘ N.end_neck.coordinate_inverse) := by
      filter_upwards [N.end_neck.carrier_open.mem_nhds he] with y hy
      simp only [axialMap, if_pos hy, Function.comp_apply, E]
    have hd := hlocal.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
    rw [mfderiv_comp x hm (hE.comp x hi), mfderiv_comp x hE hi] at hd
    have hdv : mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) N.end_neck.coordinate_map (E z) u :=
      congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hd
    have hmap : N.end_neck.coordinate_map z = x :=
      N.end_neck.coordinate_map_inverse_eq he
    have hmapE : N.axialMap f x = N.end_neck.coordinate_map (E z) :=
      hlocal.eq_of_nhds
    have hpull : roundCylinderPullback g N.end_neck.coordinate_map z w w = g.inner x v v := by
      unfold roundCylinderPullback
      rw [N.end_neck.coordinate_map_inverse_mfderiv he v]
      change g.inner (N.end_neck.coordinate_map z) v v = _
      rw [hmap]
    have hpullE : roundCylinderPullback g N.end_neck.coordinate_map (E z) u u =
        g.inner (N.axialMap f x) (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v)
          (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v) := by
      unfold roundCylinderPullback
      rw [← hdv]
      change g.inner (N.end_neck.coordinate_map (E z))
        (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v) = _
      rw [← hmapE]
    have hl := (N.end_neck.pullback_inner_comparison hz w).1
    have hu := (N.end_neck.pullback_inner_comparison hzE u).2
    have hmodel := M34.roundCylinderMetric_axial_le f z
      (hf.differentiable (by simp) z.2) (hderiv z.2) w
    change EvolvingRoundCylinderMetric 0 (E z) u u ≤
      EvolvingRoundCylinderMetric 0 z w w at hmodel
    rw [hpull] at hl
    rw [hpullE] at hu
    have ha : 0 < N.end_neck.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.end_neck.scale_pos)
    have hsq : g.inner (N.axialMap f x) (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v)
        (mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v) ≤ 4 * g.inner x v v := by
      apply (mul_le_mul_iff_right₀ ha).mp
      nlinarith
    have hnonneg : 0 ≤ g.inner x v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos x v hv).le
    change Real.sqrt _ ≤ 2 * Real.sqrt (g.inner x v v)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hnonneg]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    exact hsq
  · have hy : x ∈ N.closed_core := N.closed_core_eq_complement_end ▸ ⟨hx, he⟩
    have hlocal : N.axialMap f =ᶠ[𝓝 x] id := by
      filter_upwards [(N.recutCarrier_isOpen hc hc').mem_nhds (Or.inl hy)] with y hy
      exact N.axialMap_eq_self_on_recut hfix hy
    have hd := hlocal.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
    rw [mfderiv_id] at hd
    have hdv : mfderiv (𝓡 3) (𝓡 3) (N.axialMap f) x v = v :=
      congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => A v) hd
    rw [hdv]
    change g.tangentNorm (N.axialMap f x) v ≤ 2 * g.tangentNorm x v
    rw [N.axialMap_eq_self_of_mem_closed_core f hy]
    have hnonneg : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
    linarith

end PoincareConjecture.CapCertificate
