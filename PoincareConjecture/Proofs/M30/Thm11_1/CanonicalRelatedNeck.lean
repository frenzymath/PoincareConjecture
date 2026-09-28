import PoincareConjecture.Proofs.M30.Thm11_1.CapturedNeckTransfer
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSlice
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveComponent
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.M13.Metric
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30

private theorem canonical_rescaledMetric_eq
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (Q : ℝ) (hQ : 0 < Q) :
    rescaledMetric g Q hQ = M13.scaleSmoothMetric g Q hQ := rfl

private theorem canonical_scaled_scalar
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g) (Q : ℝ) (hQ : 0 < Q)
    (D' : LeviCivitaData (M13.scaleSmoothMetric g Q hQ)) (z : X) :
    D'.scalarCurvature z = D.scalarCurvature z / Q := by
  rw [D'.scalarCurvature_eq (rescaledMetric_connection g D Q hQ),
    rescaledMetric_scalarCurvature]
  ring

private theorem canonical_inverse_half_lt {R : ℝ} (hR : 4 < R) :
    R ^ (-1 / 2 : ℝ) < 1 / 2 := by
  calc
    _ < (4 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_lt_rpow_of_neg (by norm_num) hR (by norm_num)
    _ = _ := by norm_num [neg_div, Real.rpow_neg, ← Real.sqrt_eq_rpow]

private theorem canonical_scaled_ball
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) {Q C R rho : ℝ} (hQ : 0 < Q) (hC : 0 < C)
    (hR : 4 < R / Q) (hrho : C / 2 < rho) {x z : X}
    (hdist : g.edist x z < ENNReal.ofReal (C * R ^ (-1 / 2 : ℝ))) :
    z ∈ RiemannianMetric.ball (M13.scaleSmoothMetric g Q hQ) x rho := by
  have hRpos : 0 < R := ((div_pos_iff.mp (show 0 < R / Q by linarith)).resolve_right
    (fun h => (not_lt_of_ge hQ.le) h.2)).1
  have hpow : Real.sqrt Q * R ^ (-1 / 2 : ℝ) = (R / Q) ^ (-1 / 2 : ℝ) := by
    rw [show R / Q = Q⁻¹ * R by ring, Real.mul_rpow (inv_nonneg.mpr hQ.le) hRpos.le,
      Real.inv_rpow hQ.le, neg_div, Real.rpow_neg hQ.le, inv_inv, Real.sqrt_eq_rpow]
  have hpos : 0 < rho := (half_pos hC).trans hrho
  change RiemannianMetric.edist (M13.scaleSmoothMetric g Q hQ) x z < ENNReal.ofReal rho
  rw [← canonical_rescaledMetric_eq, rescaledMetric_edist]
  calc
    _ < ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal (C * R ^ (-1 / 2 : ℝ)) :=
      ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hQ)).ne'
        ENNReal.ofReal_ne_top hdist
    _ = ENNReal.ofReal (C * (R / Q) ^ (-1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
      congr 1
      rw [← hpow]
      ring
    _ < ENNReal.ofReal rho := (ENNReal.ofReal_lt_ofReal_iff hpos).mpr
      ((mul_lt_mul_of_pos_left (canonical_inverse_half_lt hR) hC).trans
        (by linarith))

private theorem canonical_cap_bounds
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [T3Space X]
    {g : RiemannianMetric 3 X} (A : CapCertificate g) {C : ℝ}
    (hC : A.cap_constant ≤ C) {x : X} (hx : x ∈ A.carrier) :
    1 < C ∧ (∀ z ∈ A.carrier,
      A.connection.scalarCurvature x ≤ C * A.connection.scalarCurvature z) ∧
      ∀ z ∈ A.carrier, g.edist x z <
        ENNReal.ofReal (C * A.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  obtain ⟨beta, hbeta, hratio⟩ := A.scalar_ratio
  have hxpos := A.scalar_pos x hx
  have hbetaOne : 1 ≤ beta := by nlinarith [hratio x hx x hx]
  have hCOne : 1 < C := hbetaOne.trans_lt (hbeta.trans_le hC)
  have hbounded : BddAbove (range (fun z : A.carrier => A.connection.scalarCurvature z.1)) := by
    refine ⟨beta * A.connection.scalarCurvature x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hratio x hx z.1 z.2
  have hsup : A.connection.scalarCurvature x ≤
      scalarCurvatureSupOn g A.connection A.carrier := le_csSup hbounded ⟨⟨x, hx⟩, rfl⟩
  have hpow := Real.rpow_le_rpow_of_nonpos hxpos hsup (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hdiam : intrinsicDiameter g A.carrier <
      ENNReal.ofReal (C * A.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) :=
    A.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul hC hpow
        (Real.rpow_nonneg (hxpos.le.trans hsup) _) (by linarith)))
  refine ⟨hCOne, ?_, ?_⟩
  · intro z hz
    exact (hratio z hz x hx).trans (mul_le_mul_of_nonneg_right
      (hbeta.le.trans hC) (A.scalar_pos z hz).le)
  · intro z hz
    exact ((g.edist_le_intrinsicEDist A.carrier x z).trans
      (le_sSup (show intrinsicEDist g A.carrier x z ∈
        range (fun p : A.carrier × A.carrier => intrinsicEDist g A.carrier p.1 p.2) from
          ⟨(⟨x, hx⟩, ⟨z, hz⟩), rfl⟩))).trans_lt hdiam

private theorem canonical_component_distance
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {D : LeviCivitaData g} {C : ℝ}
    (A : SingularCComponent g D C) {x : X} (hx : x ∈ A.carrier) :
    ∀ z ∈ A.carrier, g.edist x z <
      ENNReal.ofReal (C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  have hnonneg (z : A.carrier) : 0 ≤ D.scalarCurvature z.1 := by
    simpa only [mul_zero] using D.six_mul_le_scalar_of_orthonormal_sectional_lower
      z.1 (fun v w hvw => (A.positive_sectional z.1 z.2 v w hvw).le)
  have hbounded : BddBelow (range (fun z : A.carrier => D.scalarCurvature z.1 ^ (-1 / 2 : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact Real.rpow_nonneg (hnonneg z) _
  have hinf := csInf_le hbounded (show D.scalarCurvature x ^ (-1 / 2 : ℝ) ∈
    range (fun z : A.carrier => D.scalarCurvature z.1 ^ (-1 / 2 : ℝ)) from ⟨⟨x, hx⟩, rfl⟩)
  have hdiam := A.diameter_upper.trans_le (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hinf A.constant_pos.le))
  intro z hz
  exact ((g.edist_le_intrinsicEDist A.carrier x z).trans
    (le_sSup (show intrinsicEDist g A.carrier x z ∈
      range (fun p : A.carrier × A.carrier => intrinsicEDist g A.carrier p.1 p.2) from
        ⟨(⟨x, hx⟩, ⟨z, hz⟩), rfl⟩))).trans_lt hdiam

private theorem canonical_compact_target
    {M : Type v} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    {A : Set X} (hA : IsCompact A) (hopen : IsOpen A) (hne : A.Nonempty)
    (hAtarget : A ⊆ e.target) : IsCompact (univ : Set M) := by
  have hcompact : IsCompact (e.symm '' A) :=
    hA.image_of_continuousOn (e.contMDiffOn_invFun.continuousOn.mono hAtarget)
  have hopen' : IsOpen (e.symm '' A) :=
    e.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target hopen hAtarget
  have heq := (show IsClopen (e.symm '' A) from ⟨hcompact.isClosed, hopen'⟩).eq_univ
    (hne.image e.symm)
  rwa [heq] at hcompact

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_canonical_slice_related_neck_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ {M : Type v} [TopologicalSpace M] [T3Space M]
        [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        {ι : Type w} [Finite ι]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (p x : M),
        D.scalarCurvature p = 1 → 4 < D.scalarCurvature x →
      ∀ (epsilon C : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
      ∀ (F : ℕ → GeneralizedRicciFlowData.{u})
        (t Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
        (f : ∀ k, M → ((F k).slice (t k)).carrier)
        (U K : Set M),
        IsOpen U → IsPreconnected U → IsCompact K → K ⊆ U →
        p ∈ K → x ∈ K →
      ∀ (q : ι → M)
        (L : ι → Set (EuclideanSpace ℝ (Fin 3))),
        (∀ i, IsCompact (L i)) →
        (∀ i, L i ⊆ (extChartAt (𝓡 3) (q i)).target) →
        (∀ i, (extChartAt (𝓡 3) (q i)).symm '' L i ⊆ U) →
        K ⊆ ⋃ i, (extChartAt (𝓡 3) (q i)).symm '' L i →
        TendstoUniformlyOn
          (fun k y => (F k).scalar ⟨t k, f k y⟩ / Q k)
          D.scalarCurvature atTop K →
        (∀ᶠ k in atTop, Nonempty
          (GeneralizedCanonicalControl (F := F k)
            (t k) (f k x) epsilon C)) →
        let h : ∀ k, RiemannianMetric 3 ((F k).slice (t k)).carrier :=
          fun k => M13.scaleSmoothMetric ((F k).metric (t k)) (Q k) (hQ k)
        let rho := max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2) + 1
        (∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3)
            M ((F k).slice (t k)).carrier ∞,
          e.source = U ∧
          (e : M → ((F k).slice (t k)).carrier) = f k ∧
          (h k).ball (f k x) rho ⊆ f k '' K) →
        (∀ i m, m ≤ ⌊(2 * epsilon)⁻¹⌋₊ + 1 → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            ((h k).pullbackCoefficients
              (f k ∘ (extChartAt (𝓡 3) (q i)).symm)))
          (iteratedFDeriv ℝ m
            (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
          atTop (L i)) →
        (∃ V : EpsilonNeck g,
          V.epsilon = 2 * epsilon ∧ V.connection = D ∧
            D.scalarCurvature x ≤
              max 1 (2 * C) * D.scalarCurvature V.center) ∨
          IsCompact (univ : Set M) := by
  classical
  obtain ⟨epsilonRound, hRoundPos, _, hRound⟩ :=
    M28.tube.exists_round_scalar_ratio_accuracy.{u}
  refine ⟨min epsilonRound (1 / 400), lt_min hRoundPos (by norm_num),
    min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ ι _ g D p x hp hx epsilon C hepsilon hepsilon0
    F t Q hQ f U K hU hpre hK hKU hpK hxK q L hL htarget hLsource hcover
    hscalar hcanonical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  dsimp only
  intro hmaps hjets
  by_cases hcompact : IsCompact (univ : Set M)
  · exact Or.inr hcompact
  left
  let h : ∀ k, RiemannianMetric 3 ((F k).slice (t k)).carrier :=
    fun k => M13.scaleSmoothMetric ((F k).metric (t k)) (Q k) (hQ k)
  let Dsrc : ∀ k, LeviCivitaData (h k) := fun k =>
    rescaledMetric_connection ((F k).metric (t k)) ((F k).connection (t k)) (Q k) (hQ k)
  let rho := max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2) + 1
  let r := D.scalarCurvature x
  let d := max C 1
  let a := r / (2 * d)
  have hr : 4 < r := hx
  have hrpos : 0 < r := by linarith
  have hd : 1 ≤ d := le_max_right _ _
  have hdpos : 0 < d := by linarith
  have ha : 0 < a := div_pos hrpos (mul_pos (by norm_num) hdpos)
  have hepsSmall : epsilon ≤ 1 / 400 := hepsilon0.trans (min_le_right _ _)
  have hepsHalf : epsilon < 1 / 2 := by linarith
  have heta : 2 * epsilon < 1 / 2 := by linarith
  have hepsEta : epsilon < 2 * epsilon := by linarith
  have horder : ⌊(2 * epsilon)⁻¹⌋₊ + 1 ≤ ⌊epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    have hinv : 400 ≤ epsilon⁻¹ := by
      have hh := inv_anti₀ hepsilon hepsSmall
      norm_num at hh
      exact hh
    have hf : (⌊(2 * epsilon)⁻¹⌋₊ : ℝ) ≤ (2 * epsilon)⁻¹ :=
      Nat.floor_le (inv_pos.mpr (mul_pos (by norm_num) hepsilon)).le
    have heq : (2 * epsilon)⁻¹ = epsilon⁻¹ / 2 := by rw [mul_inv_rev, div_eq_mul_inv]
    rw [heq] at hf ⊢
    push_cast
    linarith
  have hDsrc (k : ℕ) (z : ((F k).slice (t k)).carrier) :
      (Dsrc k).scalarCurvature z = (F k).scalar ⟨t k, z⟩ / Q k :=
    canonical_scaled_scalar ((F k).metric (t k)) ((F k).connection (t k))
      (Q k) (hQ k) (Dsrc k) z
  have hconv : TendstoUniformlyOn
      (fun k y => (Dsrc k).scalarCurvature (f k y)) D.scalarCurvature atTop K := by
    simpa only [hDsrc] using hscalar
  obtain ⟨B, hB⟩ := hK.bddAbove_image D.continuous_scalarCurvature.continuousOn
  let b := max 1 (B + 1)
  let delta := min (r / 4) (min ((r - 4) / 2) (min (1 / 2) (r / (4 * d))))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by norm_num) (by positivity)))
  have hdelta0 : delta ≤ r / 4 := min_le_left _ _
  have hdelta1 : delta ≤ (r - 4) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdelta2 : delta ≤ 1 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta3 : delta ≤ r / (4 * d) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfloor : a ≤ 3 * r / 4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hdpos)).mpr
    nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hd)]
  have hneckRadius : (2 * Real.pi + 2 * epsilon⁻¹) / 2 < rho := by
    dsimp only [rho]
    linarith [le_max_left ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)]
  have hcapRadius : C / 2 < rho := by
    dsimp only [rho]
    linarith [le_max_right ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)]
  have htail : ∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3)
      M ((F k).slice (t k)).carrier ∞,
      e.source = U ∧ (e : M → ((F k).slice (t k)).carrier) = f k ∧
      ∃ N : EpsilonNeck (h k), N.epsilon = epsilon ∧ N.carrier ⊆ e '' K ∧
        (a ≤ (Dsrc k).scalarCurvature N.center ∧ (Dsrc k).scalarCurvature N.center ≤ b) ∧
        r ≤ max 1 (2 * C) * D.scalarCurvature (e.symm N.center) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv delta hdelta,
      hcanonical, hmaps] with k herr hcan hmap
    obtain ⟨e, hsource, he, hball⟩ := hmap
    have herror (y : M) (hy : y ∈ K) :
        |(Dsrc k).scalarCurvature (f k y) - D.scalarCurvature y| < delta := by
      simpa only [Real.dist_eq, abs_sub_comm] using herr y hy
    have hxerr := (abs_lt.mp (herror x hxK)).1
    have hperr := (abs_lt.mp (herror p hpK)).2
    have hhigh : 4 < (Dsrc k).scalarCurvature (f k x) := by
      change -delta < (Dsrc k).scalarCurvature (f k x) - r at hxerr
      linarith
    have hhighLower : 3 * r / 4 ≤ (Dsrc k).scalarCurvature (f k x) := by
      change -delta < (Dsrc k).scalarCurvature (f k x) - r at hxerr
      linarith
    have hbase : (Dsrc k).scalarCurvature (f k p) < 3 / 2 := by
      rw [hp] at hperr
      linarith
    have hhighRaw : 4 < ((F k).connection (t k)).scalarCurvature (f k x) / Q k := by
      simpa only [hDsrc, GeneralizedRicciFlowData.scalar] using hhigh
    have hxsource : x ∈ e.source := hsource.symm ▸ hKU hxK
    have hcenterData (N : EpsilonNeck (h k)) (hcap : N.carrier ⊆ e '' K) :
        e.symm N.center ∈ K ∧ f k (e.symm N.center) = N.center := by
      obtain ⟨y, hy, heq⟩ := hcap (N.central_sphere_subset N.center_on_central_sphere)
      have hinv : e.symm N.center = y := (congrArg e.symm heq).symm.trans
        (e.left_inv (hsource.symm ▸ hKU hy))
      refine ⟨hinv.symm ▸ hy, ?_⟩
      rw [hinv, ← he]
      exact heq
    have hcases : ∃ N : EpsilonNeck (h k), N.epsilon = epsilon ∧ N.carrier ⊆ e '' K ∧
        a ≤ (Dsrc k).scalarCurvature N.center ∧
        r ≤ max 1 (2 * C) * D.scalarCurvature (e.symm N.center) := by
      rcases hcan with ⟨hcan⟩
      cases hcan with
      | neck A hcenter =>
        let N : EpsilonNeck (h k) := (M28.strongNeck_top A hepsHalf).rescale (Q k) (hQ k)
        have hNeps : N.epsilon = epsilon := rfl
        have hNcenter : N.center = f k x := hcenter
        have hscale : N.scale < 1 / 2 := by
          rw [N.scale_eq_scalar, N.connection.scalarCurvature_eq (Dsrc k), hNcenter]
          exact canonical_inverse_half_lt hhigh
        have hcap : N.carrier ⊆ e '' K := by
          intro z hz
          rw [he]
          apply hball
          change (h k).edist (f k x) z < ENNReal.ofReal rho
          rw [← hNcenter]
          refine (N.edist_center_le_of_mem_carrier hz).trans_lt ?_
          rw [hNeps]
          have hcoeff : 0 < 2 * Real.pi + 2 * epsilon⁻¹ := by positivity
          have hnum : (2 * Real.pi + 2 * epsilon⁻¹) * N.scale < rho :=
            (mul_lt_mul_of_pos_left hscale hcoeff).trans (by linarith)
          exact (ENNReal.ofReal_lt_ofReal_iff
            ((half_pos hcoeff).trans hneckRadius)).mpr hnum
        refine ⟨N, hNeps, hcap, ?_, ?_⟩
        · rw [hNcenter]
          exact hfloor.trans hhighLower
        · have hinv : e.symm N.center = x := by
            rw [hNcenter, ← he]
            exact e.left_inv hxsource
          rw [hinv]
          simpa only [one_mul, r] using
            mul_le_mul_of_nonneg_right (le_max_left 1 (2 * C)) hrpos.le
      | cap A heps hconstant hconnection hxcore =>
        have hxA : f k x ∈ A.carrier := by
          rw [A.core_eq_interior_closed_core] at hxcore
          have hh := interior_subset hxcore
          rw [A.closed_core_eq_complement_end] at hh
          exact hh.1
        obtain ⟨hC, hratio, hdist⟩ := canonical_cap_bounds A hconstant hxA
        rw [hconnection] at hratio hdist
        have hdC : d = C := max_eq_left hC.le
        have hcapA : A.carrier ⊆ e '' K := by
          intro z hz
          rw [he]
          exact hball (canonical_scaled_ball ((F k).metric (t k)) (hQ k)
            (by linarith) hhighRaw hcapRadius (hdist z hz))
        let N : EpsilonNeck (h k) := A.end_neck.rescale (Q k) (hQ k)
        have hNeps : N.epsilon = epsilon := A.end_neck_epsilon.trans heps
        have hcap : N.carrier ⊆ e '' K := fun z hz => hcapA (A.end_neck_subset hz)
        have hzA : N.center ∈ A.carrier := A.end_neck_subset
          (A.end_neck.central_sphere_subset A.end_neck.center_on_central_sphere)
        have hratio' : (Dsrc k).scalarCurvature (f k x) ≤
            C * (Dsrc k).scalarCurvature N.center := by
          simp only [hDsrc, GeneralizedRicciFlowData.scalar]
          simpa only [mul_div_assoc] using
            div_le_div_of_nonneg_right (hratio N.center hzA) (hQ k).le
        have hcenter := hcenterData N hcap
        have hcenterErr := (abs_lt.mp (herror (e.symm N.center) hcenter.1)).2
        rw [hcenter.2] at hcenterErr
        have hbudget : C * delta ≤ r / 4 := by
          rw [hdC] at hdelta3
          have hh := mul_le_mul_of_nonneg_left hdelta3 (show 0 ≤ C by linarith)
          have heq : C * (r / (4 * C)) = r / 4 := by
            field_simp [ne_of_gt (show 0 < C by linarith)]
          rwa [heq] at hh
        have hrelated : r ≤ 2 * C * D.scalarCurvature (e.symm N.center) := by
          have hh := mul_lt_mul_of_pos_left hcenterErr (show 0 < C by linarith)
          nlinarith
        have hypos : 0 ≤ D.scalarCurvature (e.symm N.center) :=
          ((mul_pos_iff_of_pos_left (by linarith : 0 < 2 * C)).mp (hrpos.trans_le hrelated)).le
        refine ⟨N, hNeps, hcap, ?_, hrelated.trans
          (mul_le_mul_of_nonneg_right (le_max_right 1 (2 * C)) hypos)⟩
        change r / (2 * d) ≤ (Dsrc k).scalarCurvature N.center
        rw [hdC]
        apply (div_le_iff₀ (by linarith : 0 < 2 * C)).mpr
        nlinarith
      | component A hxA =>
        exfalso
        apply hcompact
        have hcapA : A.carrier ⊆ e '' K := by
          intro z hz
          rw [he]
          exact hball (canonical_scaled_ball ((F k).metric (t k)) (hQ k)
            A.constant_pos hhighRaw hcapRadius (canonical_component_distance A hxA z hz))
        let : LocallyConnectedSpace ((F k).slice (t k)).carrier :=
          ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
        have hopen : IsOpen A.carrier := by rw [A.component_eq]; exact isOpen_connectedComponent
        apply canonical_compact_target (M := M) (X := ((F k).slice (t k)).carrier)
          e A.compact hopen ⟨f k x, hxA⟩
        intro z hz
        obtain ⟨y, hy, rfl⟩ := hcapA hz
        exact e.map_source (hsource.symm ▸ hKU hy)
      | round A hxA =>
        exfalso
        have hpre' : IsPreconnected (e '' U) := hpre.image e
          (by simpa only [hsource] using e.contMDiffOn_toFun.continuousOn)
        have hximage : f k x ∈ e '' U := by rw [he]; exact mem_image_of_mem _ (hKU hxK)
        have hpimage : f k p ∈ e '' U := by rw [he]; exact mem_image_of_mem _ (hKU hpK)
        have hsub : e '' U ⊆ A.carrier := by
          rw [A.component_eq] at hxA ⊢
          rw [connectedComponent_eq hxA]
          exact hpre'.subset_connectedComponent hximage
        have hratio := hRound _ ((F k).metric (t k)) ((F k).connection (t k))
          epsilon A (hepsilon0.trans (min_le_left _ _)) (f k x) hxA (f k p) (hsub hpimage)
        have hratio' : (Dsrc k).scalarCurvature (f k x) ≤ 2 * (Dsrc k).scalarCurvature (f k p) := by
          simp only [hDsrc, GeneralizedRicciFlowData.scalar]
          simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hratio (hQ k).le
        linarith
    obtain ⟨N, heps, hcap, hlower, hrelated⟩ := hcases
    have hcenter := hcenterData N hcap
    have hupperErr := (abs_lt.mp (herror (e.symm N.center) hcenter.1)).2
    rw [hcenter.2] at hupperErr
    have htargetBound := hB (mem_image_of_mem D.scalarCurvature hcenter.1)
    have hupper : (Dsrc k).scalarCurvature N.center ≤ b := by
      have hb : B + 1 ≤ b := le_max_right _ _
      linarith
    exact ⟨e, hsource, he, N, heps, hcap, ⟨hlower, hupper⟩, hrelated⟩
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp htail
  have hshift (k : ℕ) := hN0 (k + N0) (Nat.le_add_left N0 k)
  choose e hsource he N heps hcap hbounds hrelated using hshift
  have hconv' : TendstoUniformlyOn
      (fun k y => (Dsrc (k + N0)).scalarCurvature (e k y)) D.scalarCurvature atTop K := by
    simpa only [he] using hconv.seq_tendstoUniformlyOn (fun k => k + N0) (tendsto_add_atTop_nat N0)
  have hjets' : ∀ i m, m ≤ ⌊(2 * epsilon)⁻¹⌋₊ + 1 → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((h (k + N0)).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm)) atTop (L i) := by
    intro i m hm
    simpa only [he] using (hjets i m hm).seq_tendstoUniformlyOn
      (fun k => k + N0) (tendsto_add_atTop_nat N0)
  have htransfer := eventually_exists_neck_of_captured_finite_metric_jets
    g D (fun k => h (k + N0)) (fun k => Dsrc (k + N0)) hepsilon hepsEta heta horder
    U hU e hsource N heps K hK hKU hcap a b ha hbounds hconv'
    q L hL htarget hLsource hcover hjets'
  obtain ⟨k, V, hVeps, hVcenter, hVconnection, _⟩ := htransfer.exists
  refine ⟨V, hVeps, hVconnection, ?_⟩
  rw [hVcenter]
  exact hrelated k

end PoincareConjecture.M30
