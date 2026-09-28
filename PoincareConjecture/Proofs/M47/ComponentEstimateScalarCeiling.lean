import PoincareConjecture.Proofs.M47.ComponentEstimateStrictHistory
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M47.ComponentEstimateCanonical
import PoincareConjecture.Proofs.M47.ComponentEstimateCrossing
import PoincareConjecture.Proofs.M47.ComponentEstimateMinimum
import PoincareConjecture.Proofs.M47.ComponentEstimatePinching
import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

private theorem scalar_sup_univ_attained
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [Nonempty M] (g : RiemannianMetric 3 M) (D : LeviCivitaData g) :
    ∃ p : M, scalarCurvatureSupOn g D univ = D.scalarCurvature p ∧
      ∀ y : M, D.scalarCurvature y ≤ D.scalarCurvature p := by
  obtain ⟨p, _hp, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (M34.contMDiff_scalarCurvature D).continuous.continuousOn
  have hbound (y : M) := hmax (mem_univ y)
  refine ⟨p, ?_, hbound⟩
  change sSup (range (fun y : (univ : Set M) => D.scalarCurvature y.val)) = _
  have hb : BddAbove (range (fun y : (univ : Set M) => D.scalarCurvature y.val)) := by
    refine ⟨D.scalarCurvature p, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hbound y.val
  apply le_antisymm
  · apply csSup_le (s := range (fun y : (univ : Set M) => D.scalarCurvature y.val))
      ⟨D.scalarCurvature p, ⟨⟨p, mem_univ p⟩, rfl⟩⟩
    rintro _ ⟨y, rfl⟩
    exact hbound y.val
  · exact le_csSup hb ⟨⟨p, mem_univ p⟩, rfl⟩





theorem exists_component_strict_scalar_duration
    (P : M47Predecessors.{u}) (PS : M47ScalarPersistencePredecessors.{u})
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ 156 * (4 * (C + 1)) * d ≤ 1 ∧
      ∀ (F : SurgeryFlowData.{u}) (origin Q : ℝ) (x : (F.slice origin).carrier),
        (F.connection origin).scalarCurvature x = Q → 6 ≤ Q → Real.exp 4 ≤ Q →
        ∀ N : SingularCComponent (F.metric origin) (F.connection origin) (2 * C),
          x ∈ N.carrier →
        ∀ (U : TopologicalSpace.Opens (F.slice origin).carrier),
          (U : Set (F.slice origin).carrier) = N.carrier →
        ∀ a : ℝ, -d / Q ≤ a → a < 0 →
        ∀ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc a 0) U,
          (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
          (∀ t ∈ Icc (origin - d / Q) origin,
            SurgeryPinchedAt (F.connection t) t) →
          (∀ t ∈ Ico (origin - d / Q) origin, ∀ y : (F.slice t).carrier,
            Q ≤ (F.connection t).scalarCurvature y →
              SurgeryCanonicalControl F t y F.parameters.epsilon C) →
          ∀ s : ℝ, ∀ hs : s ∈ Ioc a 0, ∀ y : U,
            (F.connection (origin + s / 1)).scalarCurvature
              (e.forward s ⟨hs.1.le, hs.2⟩ y.val) < 4 * (C + 1) * Q := by
  let L := 4 * (C + 1)
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨B, hB, hcanonicalBound⟩ := exists_component_crossing_analytic_bound.{u} C
  obtain ⟨tau, htau, _htau1, hexclude⟩ :=
    exists_component_maximum_exclusion_duration PS P.m13 13 B (by norm_num) hB
  let d := min 1 (min (tau / L) (1 / (156 * L)))
  have hd : 0 < d := lt_min zero_lt_one (lt_min (div_pos htau hLpos) (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hLd : L * d ≤ tau := by
    have hle : d ≤ tau / L := (min_le_right _ _).trans (min_le_left _ _)
    have h := (le_div_iff₀ hLpos).1 hle
    linarith
  have hmetricDuration : 156 * L * d ≤ 1 := by
    have hle : d ≤ 1 / (156 * L) := (min_le_right _ _).trans (min_le_right _ _)
    have h := (le_div_iff₀ (by positivity : 0 < 156 * L)).1 hle
    linarith
  refine ⟨d, hd, hd1, hmetricDuration, ?_⟩
  intro F origin Q x hxQ hQ6 hQexp N hx U hU a ha ha0 e he hpinch hcanonical
  simp only [neg_div] at ha
  have hQ : 0 < Q := by linarith
  let H := L * Q
  have hH : 0 < H := mul_pos hLpos hQ
  have hxU : x ∈ U := by change x ∈ (U : Set _); rw [hU]; exact hx
  have hcompact : IsCompact (U : Set (F.slice origin).carrier) := hU.symm ▸ N.compact
  have hconnected : IsConnected (U : Set (F.slice origin).carrier) := by
    rw [hU, N.component_eq]
    exact isConnected_connectedComponent
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨G, hread⟩ := exists_component_strict_ordinary_history P ha0 U ⟨x, hxU⟩ e
  have hterminalScalar (y : U) :
      (G.connection origin).scalarCurvature y =
        (F.connection origin).scalarCurvature y.val := by
    have hpoint : (⟨origin + 0 / 1, e.forward 0 ⟨ha0.le, le_rfl⟩ y.val⟩ :
        (t : ℝ) × (F.slice t).carrier) = ⟨origin, y.val⟩ :=
      Sigma.ext (by simp) (he _ y.val y.property)
    have hs := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hpoint
    exact (congrArg (fun t => (G.connection t).scalarCurvature y)
      (show origin + 0 / 1 = origin by simp)).symm.trans
        (((hread 0 ⟨ha0, le_rfl⟩ y).2.1).trans hs)
  have hterminalBound (y : U) : (G.connection origin).scalarCurvature y < H / 4 := by
    rw [hterminalScalar]
    have hyN : y.val ∈ N.carrier := hU ▸ y.property
    have h := twoComponent_scalar_bound N hx hxQ hyN
    have hfactor : (C / 3) * Q < H / 4 := by
      dsimp only [H, L]
      nlinarith
    exact h.trans hfactor
  let f (t : ℝ) := scalarCurvatureSupOn (G.metric t) (G.connection t) univ
  have hf : ContinuousOn f (Ioc (origin + a) origin) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (Proofs.M47.continuous_scalarSup_on_compact P.m04 G isCompact_univ)
  have hsup (t : ℝ) (y : U) : (G.connection t).scalarCurvature y ≤ f t := by
    obtain ⟨p, hp, hmax⟩ := scalar_sup_univ_attained (G.metric t) (G.connection t)
    exact (hmax y).trans_eq hp.symm
  have hfterminal : f origin < H / 4 := by
    obtain ⟨p, hp, _hmax⟩ := scalar_sup_univ_attained (G.metric origin) (G.connection origin)
    exact hp.trans_lt (hterminalBound p)
  let param (t : ℝ) := t - origin
  have hparam (t : ℝ) (ht : t ∈ Ioc (origin + a) origin) : param t ∈ Ioc a 0 := by
    dsimp only [param]
    constructor <;> linarith [ht.1, ht.2]
  have hclock (t : ℝ) : origin + param t / 1 = t := by
    simp only [param, div_one, add_sub_cancel]
  have hwindow (t : ℝ) (ht : t ∈ Ioc (origin + a) origin) :
      t ∈ Icc (origin - d / Q) origin := by
    constructor
    · have hlow : origin - d / Q ≤ origin + a := by linarith
      exact hlow.trans ht.1.le
    · exact ht.2
  have hscalar (t : ℝ) (ht : t ∈ Ioc (origin + a) origin) (y : U) :
      (G.connection t).scalarCurvature y =
        (F.connection (origin + param t / 1)).scalarCurvature
          (e.forward (param t) ⟨(hparam t ht).1.le, (hparam t ht).2⟩ y.val) :=
    (congrArg (fun v => (G.connection v).scalarCurvature y) (hclock t)).symm.trans
      (hread (param t) (hparam t ht) y).2.1
  have hnorm (t : ℝ) (ht : t ∈ Ioc (origin + a) origin) (y : U) :
      (G.connection t).curvatureTensorNorm y =
        (F.connection (origin + param t / 1)).curvatureTensorNorm
          (e.forward (param t) ⟨(hparam t ht).1.le, (hparam t ht).2⟩ y.val) :=
    (congrArg (fun v => (G.connection v).curvatureTensorNorm y) (hclock t)).symm.trans
      (hread (param t) (hparam t ht) y).2.2
  intro s hs y
  by_contra hbad
  let t0 := origin + s / 1
  have ht0 : t0 ∈ Ioc (origin + a) origin := by
    dsimp only [t0]
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2]
  have hft0 : H ≤ f t0 := by
    have hRy : H ≤ (G.connection t0).scalarCurvature y := by
      rw [(hread s hs y).2.1]
      exact le_of_not_gt hbad
    exact hRy.trans (hsup t0 y)
  have hI : Icc t0 origin ⊆ Ioc (origin + a) origin :=
    fun _ ht => ⟨ht0.1.trans_le ht.1, ht.2⟩
  obtain ⟨c, hc, hfc, hafter, _hstrict⟩ := exists_last_component_scalar_crossing ht0.2
    (hf.mono hI) hft0 (hfterminal.trans (by linarith))
  have hcJ : c ∈ Ioc (origin + a) origin := ⟨ht0.1.trans_le hc.1, hc.2.le⟩
  have hJ : Icc c origin ⊆ Ioc (origin + a) origin :=
    fun _ ht => ⟨hcJ.1.trans_le ht.1, ht.2⟩
  let Gc : RicciFlow 3 U (Icc c origin) := {
    metric := G.metric
    connection := G.connection
    interval := ordConnected_Icc
    nontrivial := ⟨c, ⟨le_rfl, hc.2.le⟩, origin, ⟨hc.2.le, le_rfl⟩, hc.2.ne⟩
    smooth := G.smooth.mono (Set.prod_mono hJ Subset.rfl)
    equation := fun t ht z v w => (G.equation t (hJ ht) z v w).mono hJ
  }
  obtain ⟨p, hp, hmax⟩ := scalar_sup_univ_attained (G.metric c) (G.connection c)
  have hpH : (Gc.connection c).scalarCurvature p = H := hp.symm.trans hfc
  have hceiling (t : ℝ) (ht : t ∈ Icc c origin) (z : U) :
      (G.connection t).scalarCurvature z ≤ H := (hsup t z).trans (hafter t ht)
  have hcurvature : ∀ t ∈ Icc c origin, ∀ z : U,
      (Gc.connection t).curvatureTensorNorm z ≤ 13 * H := by
    intro t ht z
    change (G.connection t).curvatureTensorNorm z ≤ 13 * H
    rw [hnorm t (hJ ht) z]
    apply component_pinched_curvature_bound P
      (hpinch (origin + param t / 1) (by rw [hclock]; exact hwindow t (hJ ht)))
      hQexp hL (mem_univ _)
    exact (hscalar t (hJ ht) z).symm.trans_le (hceiling t ht z)
  have hfloor : ∀ t ∈ Icc c origin, ∀ z : U,
      -H ≤ (Gc.connection t).scalarCurvature z := by
    intro t ht z
    change -H ≤ (G.connection t).scalarCurvature z
    rw [hscalar t (hJ ht) z]
    exact component_pinched_scaled_scalar_floor
      (hpinch (origin + param t / 1) (by rw [hclock]; exact hwindow t (hJ ht)))
      hQ6 hL (mem_univ _)
  obtain ⟨q, _hq, hqQ⟩ := exists_earlier_component_scalar_le PS G isCompact_univ isOpen_univ
    hc.2.le hJ (mem_univ (⟨x, hxU⟩ : U))
  rw [hterminalScalar, hxQ] at hqQ
  let sc := param c
  have hsc : sc ∈ Ioc a 0 := hparam c hcJ
  let point (z : U) := e.forward sc ⟨hsc.1.le, hsc.2⟩ z.val
  have himage : e.forward sc ⟨hsc.1.le, hsc.2⟩ '' (U : Set (F.slice origin).carrier) =
      connectedComponent (point p) :=
    component_cylinder_image_eq e U.isOpen hcompact hconnected sc _ p.property
  have hpoint (z : U) : point z ∈ connectedComponent (point p) :=
    himage ▸ mem_image_of_mem _ z.property
  have hpActual : (F.connection (origin + sc / 1)).scalarCurvature (point p) = H :=
    (hscalar c hcJ p).symm.trans hpH
  have hqActual : (F.connection (origin + sc / 1)).scalarCurvature (point q) ≤ Q :=
    (hscalar c hcJ q).symm.trans_le hqQ
  have hgap : (C / 6) * (F.connection (origin + sc / 1)).scalarCurvature (point q) ≤
      (F.connection (origin + sc / 1)).scalarCurvature (point p) := by
    rw [hpActual]
    have hmul := mul_le_mul_of_nonneg_left hqActual (by linarith : 0 ≤ C / 6)
    dsimp only [H, L]
    nlinarith
  have hmap : ContMDiff (𝓡 3) (𝓡 3) ∞ point := by
    intro z
    exact ((e.forward_smooth sc ⟨hsc.1.le, hsc.2⟩ z.val z.property).contMDiffAt
      (U.isOpen.mem_nhds z.property)).comp z (contMDiff_subtype_val (n := ∞) z)
  have hm (z : U) (v w : TangentSpace (𝓡 3) z) :
      (G.metric c).inner z v w = (F.metric (origin + sc / 1)).inner (point z)
        (mfderiv (𝓡 3) (𝓡 3) point z v) (mfderiv (𝓡 3) (𝓡 3) point z w) :=
    (congrArg (fun t => (G.metric t).inner z v w) (hclock c)).symm.trans
      ((hread sc hsc z).1 v w).symm
  have hgradient : ∀ z : U, 3 * H / 4 ≤ (Gc.connection c).scalarCurvature z →
      ∀ v : TangentSpace (𝓡 3) z, (Gc.metric c).inner z v v = 1 →
        |mvfderiv (𝓡 3) (Gc.connection c).scalarCurvature z v| ≤
          B * (Gc.connection c).scalarCurvature z ^ (3 / 2 : ℝ) := by
    intro z hz v hv
    have hzQ : Q ≤ (F.connection (origin + sc / 1)).scalarCurvature (point z) := by
      have hfactor : Q ≤ 3 * H / 4 := by dsimp only [H, L]; nlinarith
      exact (hfactor.trans hz).trans_eq (hscalar c hcJ z)
    have hcWindow : origin + sc / 1 ∈ Ico (origin - d / Q) origin := by
      rw [hclock c]
      exact ⟨(hwindow c hcJ).1, hc.2⟩
    have hcan := hcanonical (origin + sc / 1) hcWindow (point z) hzQ
    have hestimate := hcanonicalBound F (origin + sc / 1) (point p) (point q)
      (point z) (hpoint q) (hpoint z) hgap hcan
    have hunit : (F.metric (origin + sc / 1)).inner (point z)
        (mfderiv (𝓡 3) (𝓡 3) point z v) (mfderiv (𝓡 3) (𝓡 3) point z v) = 1 :=
      (hm z v v).symm.trans hv
    have hdifferential := M45.model_scalar_differential_eq_of_local_isometry
      (G.connection c) (F.connection (origin + sc / 1)) isOpen_univ hmap.contMDiffOn
      (fun w _hw => hm w) (mem_univ z) v
    change |mvfderiv (𝓡 3) (G.connection c).scalarCurvature z v| ≤
      B * (G.connection c).scalarCurvature z ^ (3 / 2 : ℝ)
    rw [hdifferential, hscalar c hcJ z]
    exact ((F.connection (origin + sc / 1)).abs_scalar_directional_le_scalarGradientNorm
      (point z) _ hunit).trans hestimate.2.1
  have hshort : H * (origin - c) ≤ tau := by
    have hcLower := (hwindow c hcJ).1
    have htime : (origin - c) * Q ≤ d := (le_div_iff₀ hQ).1 (by linarith : origin - c ≤ d / Q)
    have hscaled := mul_le_mul_of_nonneg_left htime hLpos.le
    dsimp only [H]
    nlinarith [hLd]
  have hne := hexclude U c origin H hc.2 hH Gc hcurvature hfloor
    (hceiling c ⟨le_rfl, hc.2.le⟩) hgradient hshort hterminalBound p
  exact hne hpH

end PoincareConjecture.M47
