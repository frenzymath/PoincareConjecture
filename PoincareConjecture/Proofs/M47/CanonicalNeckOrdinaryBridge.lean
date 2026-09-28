import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem neck_scale_inverse_square
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) :
    N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
  rw [N.scale_eq_scalar, inv_pow,
    ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
  norm_num [Real.rpow_neg_one]

theorem exists_strong_neck_of_ordinary_family
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin a b t : ℝ}
    (e : SurgeryFlowCylinder F C origin 1 (Icc a b) univ)
    (G : RicciFlow 3 C.carrier (Icc (origin + a) (origin + b)))
    (hmetric : ∀ (s : ℝ) (hs : s ∈ Icc a b) (x : C.carrier)
      (v w : TangentSpace (𝓡 3) x),
      e.pullbackInner s hs x v w = (G.metric (origin + s / 1)).inner x v w)
    (N : EpsilonNeck (G.metric t)) (hconnection : N.connection = G.connection t)
    (htimes : ∀ u ∈ Ioc (-1 : ℝ) 0,
      t + u / (N.scale⁻¹ ^ 2) ∈ Icc (origin + a) (origin + b))
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback (G.metric (t + u / (N.scale⁻¹ ^ 2)))
          N.coordinate_map z v w)) :
    ∃ S : SurgeryStrongNeck F t N.epsilon, ∃ ht : t - origin ∈ Icc a b,
      HEq S.neck.center (e.forward (t - origin) ht N.center) := by
  let Q := N.scale⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  let phi : ℝ → ℝ := fun u => t - origin + u / Q
  have hmem : MapsTo phi (Ioc (-1 : ℝ) 0) (Icc a b) := by
    intro u hu
    have ht := htimes u hu
    change t + u / Q ∈ Icc (origin + a) (origin + b) at ht
    dsimp only [phi]
    constructor <;> linarith only [ht.1, ht.2]
  have hmono : StrictMonoOn phi (Ioc (-1 : ℝ) 0) := by
    intro s _hs r _hr hsr
    have hdiv := div_lt_div_of_pos_right hsr hQ
    dsimp only [phi]
    linarith only [hdiv]
  have hclock : ∀ u ∈ Ioc (-1 : ℝ) 0, t + u / Q = origin + phi u / 1 := by
    intro u _hu
    simp only [phi, div_one]
    ring
  let shifted := seedCylinderReclock e hQ ordConnected_Ioc phi hmem hmono hclock
  let d := shifted.restrict (Subset.refl _) ordConnected_Ioc (subset_univ N.carrier)
  have hread (u : ℝ) (hu : u ∈ Ioc (-1 : ℝ) 0) (x : C.carrier)
      (v w : TangentSpace (𝓡 3) x) :
      shifted.pullbackInner u hu x v w = Q * (G.metric (t + u / Q)).inner x v w := by
    rw [neck_reclock_pullbackInner, div_one, hmetric, ← hclock u hu]
  have hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hmetric0 (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
      (G.metric t).inner x v w = (F.metric (t + 0 / Q)).inner (shifted.forward 0 hzero x)
        (mfderiv (𝓡 3) (𝓡 3) (shifted.forward 0 hzero) x v)
        (mfderiv (𝓡 3) (𝓡 3) (shifted.forward 0 hzero) x w) := by
    have hm := hread 0 hzero x v w
    change Q * (F.metric (t + 0 / Q)).inner (shifted.forward 0 hzero x)
      (mfderiv (𝓡 3) (𝓡 3) (shifted.forward 0 hzero) x v)
      (mfderiv (𝓡 3) (𝓡 3) (shifted.forward 0 hzero) x w) =
        Q * (G.metric (t + 0 / Q)).inner x v w at hm
    have hcancel := (mul_left_cancel₀ hQ.ne') hm
    have ht0 : (G.metric (t + 0 / Q)).inner x v w = (G.metric t).inner x v w := by simp
    exact (hcancel.trans ht0).symm
  have hscalar : (F.connection (t + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (d.forward 0 hzero N.center) = N.connection.scalarCurvature N.center := by
    rw [hconnection]
    exact ((G.connection t).scalarCurvature_eq_of_local_isometry
      (F.connection (t + 0 / Q)) isOpen_univ (shifted.forward_smooth 0 hzero)
      (fun x _hx v w => hmetric0 x v w) (mem_univ N.center)).symm
  have hcomparison : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback d N.coordinate_map) := by
    apply hfamily.congr_cylinder
    intro u hu z _hz v w
    simp only [surgeryCylinderPullback, dif_pos hu]
    exact (hread u hu (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)).symm
  obtain ⟨S, hcenter⟩ := exists_physical_strong_neck_of_family N d hscalar hcomparison
  have hphi0 : phi 0 = t - origin := by simp only [phi, zero_div, add_zero]
  have ht : t - origin ∈ Icc a b := hphi0 ▸ hmem hzero
  have he := seedCylinderReclock_forward_heq e hQ ordConnected_Ioc phi
    hmem hmono hclock 0 hzero N.center
  have hold : HEq (e.forward (phi 0) (hmem hzero) N.center)
      (e.forward (t - origin) ht N.center) := by
    have hparam : ∀ s (hs : s ∈ Icc a b), s = t - origin →
        HEq (e.forward s hs N.center) (e.forward (t - origin) ht N.center) := by
      intro s hs hst
      subst s
      rfl
    exact hparam _ _ hphi0
  have hout : ∃ S : SurgeryStrongNeck F (t + 0 / Q) N.epsilon,
      ∃ ht : t - origin ∈ Icc a b,
        HEq S.neck.center (e.forward (t - origin) ht N.center) :=
    ⟨S, ht, (heq_of_eq hcenter).trans (he.trans hold)⟩
  have htransport : ∀ t' : ℝ, t' = t →
      (∃ S : SurgeryStrongNeck F t' N.epsilon, ∃ ht : t - origin ∈ Icc a b,
        HEq S.neck.center (e.forward (t - origin) ht N.center)) →
      ∃ S : SurgeryStrongNeck F t N.epsilon, ∃ ht : t - origin ∈ Icc a b,
        HEq S.neck.center (e.forward (t - origin) ht N.center) := by
    intro t' ht' h
    subst t'
    exact h
  exact htransport _ (by simp only [zero_div, add_zero]) hout

end PoincareConjecture.Proofs.M47
