import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOlderFamily
import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M47.CanonicalNeckSourceTransfer
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingNeck











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem olderOrdinary_native_readout
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    (U : TopologicalSpace.Opens C.carrier) {origin q s H : ℝ} {I : Set ℝ}
    (e : SurgeryFlowCylinder F C origin q I U) (hs : s ∈ I)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = H * e.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    {g0 : RiemannianMetric 3 U} (N0 : EpsilonNeck g0)
    (hepsilon : N0.epsilon = N.epsilon)
    (hcoordinate : ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → (N0.coordinate_map z).val = N.coordinate_map z)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback gU N0.coordinate_map z v w =
      H * surgeryCylinderPullback e N.coordinate_map s z v w := by
  have hz0 : z.2 ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹ := hepsilon.symm ▸ hz
  have hN0 := (N0.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz0⟩)).mdifferentiableAt (by simp)
  have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : U → C.carrier) (N0.coordinate_map z) :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have heq : (Subtype.val : U → C.carrier) ∘ N0.coordinate_map =ᶠ[𝓝 z] N.coordinate_map := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from ⟨mem_univ _, hz⟩)] with p hp
    exact hcoordinate p hp.2
  have hderiv := (mfderiv_comp z hsub hN0).symm.trans heq.mfderiv_eq
  have hv := congrArg (fun L => L v) hderiv
  have hw := congrArg (fun L => L w) hderiv
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (N0.coordinate_map z)
    (mfderiv Ic (𝓡 3) N0.coordinate_map z v) = mfderiv Ic (𝓡 3) N.coordinate_map z v at hv
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (N0.coordinate_map z)
    (mfderiv Ic (𝓡 3) N0.coordinate_map z w) = mfderiv Ic (𝓡 3) N.coordinate_map z w at hw
  have hr := hmetric (N0.coordinate_map z)
    (mfderiv Ic (𝓡 3) N0.coordinate_map z v) (mfderiv Ic (𝓡 3) N0.coordinate_map z w)
  rw [hv, hw, hcoordinate z hz] at hr
  simpa only [roundCylinderPullback, surgeryCylinderPullback, dif_pos hs,
    SurgeryFlowCylinder.pullbackInner] using hr



theorem exists_source_initial_older_ordinary
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {T q k H tau dr : ℝ} (hk : 0 < k) (hH : 0 < H) (htau : 0 < tau)
    (hscale : N.scale⁻¹ ^ 2 = q * k)
    (hclock : MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-tau) 0))
    (e : SurgeryFlowCylinder F C T q (Icc (-tau) 0) N.carrier)
    (hzero : ∀ hz, ∀ x ∈ N.carrier, ∀ v w : TangentSpace (𝓡 3) x,
      e.pullbackInner 0 hz x v w = q * g.inner x v w)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Icc (-1 : ℝ) 0)
      (fun u z v w => k * surgeryCylinderPullback e N.coordinate_map (u / k) z v w)) :
    let U : TopologicalSpace.Opens C.carrier := ⟨N.carrier, N.carrier_open⟩
    ∃ G : RicciFlow 3 U (Ioc (-(dr + H * tau)) (-dr)),
      ∃ older : SurgeryOrdinaryStrongNeck (neckOpenSourceCarrier U) G (-dr) N.epsilon,
        older.neck.center.val = N.center ∧ older.neck.carrier = univ ∧
        older.neck.scale ^ 2 = H / k ∧
        (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          (older.neck.coordinate_map z).val = N.coordinate_map z) ∧
        ∀ u ∈ Icc (-(dr + H * tau)) (-dr), ∀ hu : (u + dr) / H ∈ Icc (-tau) 0,
          ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
            (G.metric u).inner x v w = H * e.pullbackInner ((u + dr) / H) hu x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
  let U : TopologicalSpace.Opens C.carrier := ⟨N.carrier, N.carrier_open⟩
  have hne : (U : Set C.carrier).Nonempty :=
    ⟨N.center, N.central_sphere_subset N.center_on_central_sphere⟩
  obtain ⟨G0, hG0⟩ := terminalSourceRealization_surgery P htau U hne e
  let I : SpacetimeInterval := {
    domain := Icc (-tau) 0
    ordConnected := G0.interval
    nontrivial := G0.nontrivial }
  obtain ⟨R⟩ := M13.ordinaryParabolicRescaling I G0 H hH (dr / H)
  have hrawTime (u : ℝ) : parabolicTimeInv H (dr / H) u = (u + dr) / H := by
    dsimp only [parabolicTimeInv]
    ring
  have htimes : MapsTo (fun u : ℝ => (u + dr) / H)
      (Icc (-(dr + H * tau)) (-dr)) (Icc (-tau) 0) := by
    intro u hu
    constructor
    · apply (le_div_iff₀ hH).mpr
      nlinarith only [hu.1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hu.2]) hH.le
  have hsub : Ioc (-(dr + H * tau)) (-dr) ⊆ (parabolicInterval H hH (dr / H) I).domain := by
    intro u hu
    apply (mem_parabolicInterval_iff H hH (dr / H) I u).mpr
    rw [hrawTime]
    exact htimes ⟨hu.1.le, hu.2⟩
  have hspan : 0 < H * tau := mul_pos hH htau
  let G : RicciFlow 3 U (Ioc (-(dr + H * tau)) (-dr)) := {
    metric := R.flow.metric
    connection := R.flow.connection
    interval := ordConnected_Ioc
    nontrivial := ⟨-dr - H * tau / 2, ⟨by linarith only [hspan], by linarith only [hspan]⟩,
      -dr, ⟨by linarith only [hspan], le_rfl⟩, by linarith only [hspan]⟩
    smooth := R.flow.smooth.mono (Set.prod_mono hsub Subset.rfl)
    equation := fun t ht x v w => (R.flow.equation t (hsub ht) x v w).mono hsub }
  have hread (u : ℝ) (hu : u ∈ Icc (-(dr + H * tau)) (-dr))
      (hraw : (u + dr) / H ∈ Icc (-tau) 0) (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G.metric u).inner x v w = H * e.pullbackInner ((u + dr) / H) hraw x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
    have hm := R.metric_eq u x v w
    rw [hrawTime, (hG0 _ (htimes hu) x).1 v w] at hm
    exact hm
  have hq : 0 < q := e.scale_pos
  have hQ : 0 < q * H := mul_pos hq hH
  let scaled := N.scaleMetric (q * H) hQ
  have hjoin : (-dr : ℝ) ∈ Icc (-(dr + H * tau)) (-dr) :=
    ⟨by linarith only [hspan], le_rfl⟩
  have hzeroMem : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith only [htau], le_rfl⟩
  have hjoinMetric (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G.metric (-dr)).inner x v w = (M13.scaleSmoothMetric g (q * H) hQ).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
    have hm := hread (-dr) hjoin (htimes hjoin) x v w
    simp only [neg_add_cancel, zero_div] at hm
    rw [hm, hzero hzeroMem x.val x.property, M13.scaleSmoothMetric_inner]
    ring
  obtain ⟨N0, hepsilon, hNscale, hconnection, hcenter, hcarrier, hcoordinate⟩ :=
    exists_full_open_source_neck scaled U rfl (G.metric (-dr)) (G.connection (-dr)) hjoinMetric
  have hscaleSq : N0.scale ^ 2 = H / k := by
    rw [hNscale]
    change (Real.sqrt (q * H) * N.scale) ^ 2 = H / k
    rw [mul_pow, Real.sq_sqrt hQ.le]
    have hprod : N.scale ^ 2 * (q * k) = 1 := by
      rw [← hscale, ← mul_pow, mul_inv_cancel₀ N.scale_pos.ne', one_pow]
    apply (eq_div_iff hk.ne').mpr
    calc
      (q * H * N.scale ^ 2) * k = H * (N.scale ^ 2 * (q * k)) := by ring
      _ = H := by rw [hprod, mul_one]
  have hinvScale : N0.scale⁻¹ ^ 2 = k / H := by rw [inv_pow, hscaleSq, inv_div]
  have hbottom : 1 / k ≤ tau := by
    have h := (hclock (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 0 from ⟨le_rfl, by norm_num⟩)).1
    change -tau ≤ -1 / k at h
    rw [neg_div] at h
    linarith only [h]
  have hbackward : Ioc (-dr - N0.scale ^ 2) (-dr) ⊆ Ioc (-(dr + H * tau)) (-dr) := by
    intro t ht
    rw [hscaleSq] at ht
    have hmul := mul_le_mul_of_nonneg_left hbottom hH.le
    have hdiv : H * (1 / k) = H / k := by ring
    rw [hdiv] at hmul
    exact ⟨by linarith only [ht.1, hmul], ht.2⟩
  have hcomparison : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => N0.scale⁻¹ ^ 2 *
        roundCylinderPullback (G.metric (-dr + s * N0.scale ^ 2)) N0.coordinate_map z v w) := by
    have hf : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
        (fun u z v w => k * surgeryCylinderPullback e N.coordinate_map (u / k) z v w) := by
      obtain ⟨hs, bound, hb, hbound⟩ := hfamily
      exact ⟨fun u hu => hs u ⟨hu.1.le, hu.2⟩, bound, hb,
        fun u hu => hbound u ⟨hu.1.le, hu.2⟩⟩
    apply hf.congr_cylinder
    intro s hs z hz v w
    have ht : -dr + s * N0.scale ^ 2 ∈ Icc (-(dr + H * tau)) (-dr) := by
      have ht' := hbackward (show -dr + s * N0.scale ^ 2 ∈ Ioc (-dr - N0.scale ^ 2) (-dr) from
        ⟨by nlinarith only [hs.1, sq_pos_of_pos N0.scale_pos],
          by nlinarith only [hs.2, sq_nonneg N0.scale]⟩)
      exact ⟨ht'.1.le, ht'.2⟩
    have htime : ((-dr + s * N0.scale ^ 2) + dr) / H = s / k := by
      rw [hscaleSq]
      field_simp
      ring
    have hm : ∀ x : U, ∀ a b : TangentSpace (𝓡 3) x,
        (G.metric (-dr + s * N0.scale ^ 2)).inner x a b = H *
          e.pullbackInner (s / k) (hclock ⟨hs.1.le, hs.2⟩) x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x a)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x b) := by
      intro x a b
      have h := hread _ ht (htimes ht) x a b
      simpa only [htime] using h
    have hn := olderOrdinary_native_readout N U e (hclock ⟨hs.1.le, hs.2⟩)
      (G.metric (-dr + s * N0.scale ^ 2)) hm N0 hepsilon hcoordinate z hz v w
    rw [hn, hinvScale]
    field_simp
  let older : SurgeryOrdinaryStrongNeck (neckOpenSourceCarrier U) G (-dr) N.epsilon := {
    neck := N0
    epsilon_eq := hepsilon
    connection_eq := hconnection
    backward_subset := hbackward
    comparison := hcomparison }
  exact ⟨G, older, hcenter, hcarrier, hscaleSq, hcoordinate, hread⟩

end PoincareConjecture.M47
