import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalSliceRound
import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalSliceCap
import PoincareConjecture.Proofs.M30.Thm11_8.CanonicalSliceMetricComparison
import PoincareConjecture.Proofs.M30.Thm11_1.CapturedNeckTransfer
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSlice
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveComponent
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundUniformScalar
import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.RelativeMetricReadout
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30

private theorem shape_inverse_half_lt {R : ℝ} (hR : 4 < R) :
    R ^ (-1 / 2 : ℝ) < 1 / 2 := by
  calc
    _ < (4 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_lt_rpow_of_neg (by norm_num) hR (by norm_num)
    _ = _ := by norm_num [neg_div, Real.rpow_neg, ← Real.sqrt_eq_rpow]

private theorem shape_scaled_ball
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
  change RiemannianMetric.edist (rescaledMetric g Q hQ) x z < ENNReal.ofReal rho
  rw [rescaledMetric_edist]
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
      ((mul_lt_mul_of_pos_left (shape_inverse_half_lt hR) hC).trans (by linarith))

private theorem shape_cap_bounds
    {X : Type u} [TopologicalSpace X] [T3Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    [MeasurableSpace X] [BorelSpace X]
    {g : RiemannianMetric 3 X} (A : CapCertificate g) {C : ℝ}
    (hC : A.cap_constant ≤ C) {x : X} (hx : x ∈ A.carrier) :
    1 < C ∧ (∀ y ∈ A.carrier, ∀ z ∈ A.carrier,
      A.connection.scalarCurvature y ≤ C * A.connection.scalarCurvature z) ∧
      ∀ z ∈ A.carrier, intrinsicEDist g A.carrier x z <
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
  · intro y hy z hz
    exact (hratio z hz y hy).trans (mul_le_mul_of_nonneg_right
      (hbeta.le.trans hC) (A.scalar_pos z hz).le)
  · intro z hz
    exact (le_sSup (show intrinsicEDist g A.carrier x z ∈
      range (fun p : A.carrier × A.carrier => intrinsicEDist g A.carrier p.1 p.2) from
        ⟨(⟨x, hx⟩, ⟨z, hz⟩), rfl⟩)).trans_lt hdiam

private theorem shape_component_distance
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

private theorem shape_compact_target
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

set_option maxHeartbeats 1000000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_canonical_slice_shape_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ {M : Type v} [TopologicalSpace M] [T3Space M]
        [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M]
        {ι : Type w} [Finite ι]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (x : M), 4 < D.scalarCurvature x →
      ∀ (epsilon C : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
      ∀ (F : ℕ → GeneralizedRicciFlowData.{u})
        (t Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
        (f : ∀ k, M → ((F k).slice (t k)).carrier)
        (U K : Set M),
        IsOpen U → IsCompact K → K ⊆ U → x ∈ K →
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
        let rho :=
          max (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8 + 1
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
        (∃ N : EpsilonNeck g,
          N.epsilon = 2 * epsilon ∧ N.connection = D ∧ N.center = x) ∨
        (∃ N : EpsilonNeck g, ∃ W : Set M,
          N.epsilon = 2 * epsilon ∧ N.connection = D ∧
          IsOpen W ∧ IsCompact (closure W) ∧ x ∈ W ∧ x ∉ N.carrier ∧
          frontier W = N.central_sphere ∧
          W ∩ N.carrier = N.region (-N.epsilon⁻¹) 0 ∧
          closure W ⊆ g.ball x
            (8 * max 1 C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) ∧
          (4 * max 1 C * D.scalarCurvature x)⁻¹ ≤ N.scale ^ 2 ∧
          N.scale ^ 2 ≤ 4 * max 1 C / D.scalarCurvature x) ∨
        IsCompact (univ : Set M) := by
  classical
  obtain ⟨epsilonRound, hRoundPos, _, hRound⟩ :=
    M28.tube.exists_round_scalar_accuracy.{u} (show (0 : ℝ) < 1 by norm_num)
  refine ⟨min epsilonRound (1 / 400), lt_min hRoundPos (by norm_num),
    min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ ι _ g D x hx epsilon C hepsilon hepsilon0
    F t Q hQ f U K hU hK hKU hxK q L hL htarget hLsource hcover hscalar hcanonical
  dsimp only
  intro hmaps hjets
  by_cases hcompact : IsCompact (univ : Set M)
  · exact Or.inr (Or.inr hcompact)
  let h : ∀ k, RiemannianMetric 3 ((F k).slice (t k)).carrier :=
    fun k => M13.scaleSmoothMetric ((F k).metric (t k)) (Q k) (hQ k)
  let Dsrc : ∀ k, LeviCivitaData (h k) := fun k =>
    rescaledMetric_connection ((F k).metric (t k)) ((F k).connection (t k)) (Q k) (hQ k)
  let rho := max (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8 + 1
  let r := D.scalarCurvature x
  let d := max 1 C
  let a := r / (2 * d)
  let b := 2 * d * r
  let Result : Prop :=
    (∃ N : EpsilonNeck g, N.epsilon = 2 * epsilon ∧ N.connection = D ∧ N.center = x) ∨
    (∃ N : EpsilonNeck g, ∃ W : Set M,
      N.epsilon = 2 * epsilon ∧ N.connection = D ∧
      IsOpen W ∧ IsCompact (closure W) ∧ x ∈ W ∧ x ∉ N.carrier ∧
      frontier W = N.central_sphere ∧ W ∩ N.carrier = N.region (-N.epsilon⁻¹) 0 ∧
      closure W ⊆ g.ball x (8 * d * r ^ (-1 / 2 : ℝ)) ∧
      (4 * d * r)⁻¹ ≤ N.scale ^ 2 ∧ N.scale ^ 2 ≤ 4 * d / r)
  have hr : 4 < r := hx
  have hrpos : 0 < r := by linarith
  have hd : 1 ≤ d := le_max_left _ _
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
      (Dsrc k).scalarCurvature z = (F k).scalar ⟨t k, z⟩ / Q k := by
    change (rescaledMetric_connection _ _ _ _).scalarCurvature z = _
    rw [rescaledMetric_scalarCurvature]
    change _ = ((F k).connection (t k)).scalarCurvature z / Q k
    ring
  have hconv : TendstoUniformlyOn
      (fun k y => (Dsrc k).scalarCurvature (f k y)) D.scalarCurvature atTop K := by
    simpa only [hDsrc] using hscalar
  let delta := min (r / 4) (min ((r - 4) / 2) (r / (4 * d)))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdelta0 : delta ≤ r / 4 := min_le_left _ _
  have hdelta1 : delta ≤ (r - 4) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdelta2 : delta ≤ r / (4 * d) := (min_le_right _ _).trans (min_le_right _ _)
  have hquarter : 0 < r / (4 * d) := by positivity
  have haquarter : a = 2 * (r / (4 * d)) := by dsimp only [a]; ring
  have hfloor : a ≤ r / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d)).mpr
    nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hd)]
  have hupper : 2 * r ≤ b := by
    dsimp only [b]
    nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hd)]
  have hneckRadius : (2 * Real.pi + 2 * epsilon⁻¹) / 2 < rho := by
    have h1 := le_max_left ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)
    have h2 := le_max_left (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8
    dsimp only [rho]
    linarith
  have hcapRadius : C / 2 < rho := by
    have h1 := le_max_right ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)
    have h2 := le_max_left (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8
    dsimp only [rho]
    linarith
  have hroundRadius : 8 < rho := by
    dsimp only [rho]
    linarith [le_max_right (max ((2 * Real.pi + 2 * epsilon⁻¹) / 2) (C / 2)) 8]
  have htail : ∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3)
      M ((F k).slice (t k)).carrier ∞,
      e.source = U ∧ (e : M → ((F k).slice (t k)).carrier) = f k ∧
      ∃ N : EpsilonNeck (h k), N.epsilon = epsilon ∧ N.carrier ⊆ e '' K ∧
        (a ≤ (Dsrc k).scalarCurvature N.center ∧ (Dsrc k).scalarCurvature N.center ≤ b) ∧
        ∀ V : EpsilonNeck g, V.epsilon = 2 * epsilon → V.connection = D →
          V.center = e.symm N.center → V.coordinate_map = e.symm ∘ N.coordinate_map →
          (∀ z ∈ e '' K, ∀ w : TangentSpace (𝓡 3) z,
            g.tangentNorm (e.symm z) (mfderiv (𝓡 3) (𝓡 3) e.symm z w) ≤
              2 * (h k).tangentNorm z w) → Result := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv delta hdelta,
      hcanonical, hmaps] with k herr hcan hmap
    obtain ⟨e, hsource, he, hball⟩ := hmap
    have herror (y : M) (hy : y ∈ K) :
        |(Dsrc k).scalarCurvature (f k y) - D.scalarCurvature y| < delta := by
      simpa only [Real.dist_eq, abs_sub_comm] using herr y hy
    have hxerr := abs_lt.mp (herror x hxK)
    change -delta < (Dsrc k).scalarCurvature (f k x) - r ∧
      (Dsrc k).scalarCurvature (f k x) - r < delta at hxerr
    have hhigh : 4 < (Dsrc k).scalarCurvature (f k x) := by linarith
    have hlowerSrc : r / 2 ≤ (Dsrc k).scalarCurvature (f k x) := by linarith
    have hupperSrc : (Dsrc k).scalarCurvature (f k x) ≤ 2 * r := by linarith
    have hhighRaw : 4 < ((F k).connection (t k)).scalarCurvature (f k x) / Q k := by
      simpa only [hDsrc, GeneralizedRicciFlowData.scalar] using hhigh
    have hxsource : x ∈ e.source := hsource.symm ▸ hKU hxK
    have himageTarget : e '' K ⊆ e.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact e.map_source (hsource.symm ▸ hKU hy)
    refine ⟨e, hsource, he, ?_⟩
    rcases hcan with ⟨hcan⟩
    cases hcan with
    | neck A hcenter =>
      let N : EpsilonNeck (h k) := (M28.strongNeck_top A hepsHalf).rescale (Q k) (hQ k)
      have hNeps : N.epsilon = epsilon := rfl
      have hNcenter : N.center = f k x := hcenter
      have hscale : N.scale < 1 / 2 := by
        rw [N.scale_eq_scalar, N.connection.scalarCurvature_eq (Dsrc k), hNcenter]
        exact shape_inverse_half_lt hhigh
      have hcap : N.carrier ⊆ e '' K := by
        intro z hz
        rw [he]
        apply hball
        change (h k).edist (f k x) z < ENNReal.ofReal rho
        rw [← hNcenter]
        refine (N.edist_center_le_of_mem_carrier hz).trans_lt ?_
        rw [hNeps]
        have hcoeff : 0 < 2 * Real.pi + 2 * epsilon⁻¹ := by positivity
        exact (ENNReal.ofReal_lt_ofReal_iff ((half_pos hcoeff).trans hneckRadius)).mpr
          ((mul_lt_mul_of_pos_left hscale hcoeff).trans (by linarith))
      refine ⟨N, hNeps, hcap, ?_, ?_⟩
      · rw [hNcenter]
        exact ⟨hfloor.trans hlowerSrc, hupperSrc.trans hupper⟩
      · intro V hVeps hVconn hVcenter _hVcoord _hnorm
        apply Or.inl
        refine ⟨V, hVeps, hVconn, ?_⟩
        rw [hVcenter, hNcenter, ← he]
        exact e.left_inv hxsource
    | cap A heps hconstant hconnection hxcore =>
      have hxA : f k x ∈ A.carrier :=
        (A.closed_core_eq_complement_end ▸
          interior_subset (A.core_eq_interior_closed_core ▸ hxcore)).1
      obtain ⟨hC, hratio, hintrinsic⟩ := shape_cap_bounds A hconstant hxA
      have hCpos : 0 < C := by linarith
      have hdC : d = C := max_eq_right hC.le
      have hcapA : A.carrier ⊆ e '' K := by
        intro z hz
        rw [he]
        apply hball
        apply shape_scaled_ball ((F k).metric (t k)) (hQ k) hCpos hhighRaw hcapRadius
        have hh := (((F k).metric (t k)).edist_le_intrinsicEDist A.carrier (f k x) z).trans_lt
          (hintrinsic z hz)
        simpa only [hconnection] using hh
      let N : EpsilonNeck (h k) := A.end_neck.rescale (Q k) (hQ k)
      have hNeps : N.epsilon = epsilon := A.end_neck_epsilon.trans heps
      have hcap : N.carrier ⊆ e '' K := fun z hz => hcapA (A.end_neck_subset hz)
      have hzA : N.center ∈ A.carrier := A.end_neck_subset
        (A.end_neck.central_sphere_subset A.end_neck.center_on_central_sphere)
      have hratioForward : (Dsrc k).scalarCurvature (f k x) ≤
          C * (Dsrc k).scalarCurvature N.center := by
        simp only [hDsrc, GeneralizedRicciFlowData.scalar]
        have hh := hratio (f k x) hxA N.center hzA
        rw [hconnection] at hh
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (hQ k).le
      have hratioBack : (Dsrc k).scalarCurvature N.center ≤
          C * (Dsrc k).scalarCurvature (f k x) := by
        simp only [hDsrc, GeneralizedRicciFlowData.scalar]
        have hh := hratio N.center hzA (f k x) hxA
        rw [hconnection] at hh
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (hQ k).le
      have hbounds : a ≤ (Dsrc k).scalarCurvature N.center ∧
          (Dsrc k).scalarCurvature N.center ≤ b := by
        constructor
        · dsimp only [a]
          rw [hdC]
          apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
          nlinarith
        · dsimp only [b]
          rw [hdC]
          nlinarith
      refine ⟨N, hNeps, hcap, hbounds, ?_⟩
      intro V hVeps hVconn hVcenter hVcoord hnorm
      have hrawpos := A.scalar_pos (f k x) hxA
      have hboundRaw (z : ((F k).slice (t k)).carrier) (hz : z ∈ A.carrier)
          (w : TangentSpace (𝓡 3) z) :
          g.tangentNorm (e.symm z) (mfderiv (𝓡 3) (𝓡 3) e.symm z w) ≤
            (2 * Real.sqrt (Q k)) * ((F k).metric (t k)).tangentNorm z w := by
        have hh := hnorm z (hcapA hz) w
        rw [M13.scaleSmoothMetric_tangentNorm] at hh
        simpa only [mul_assoc] using hh
      obtain ⟨W, hWopen, hWcompact, hxW, hxNot, hfront, hoverlap, hWball⟩ :=
        exists_cap_side_of_inverse_neck_coordinates g ((F k).metric (t k)) A e
          (hcapA.trans himageTarget) V
          (by rw [heps, hVeps]; linarith) hVcoord hxsource
          (by simpa only [he] using hxcore)
          (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hQ k)))
          (mul_pos hCpos (Real.rpow_pos_of_pos hrawpos _)) hboundRaw
          (by intro z hz; simpa only [he] using hintrinsic z hz)
      have hpow : Real.sqrt (Q k) * A.connection.scalarCurvature (f k x) ^ (-1 / 2 : ℝ) =
          ((Dsrc k).scalarCurvature (f k x)) ^ (-1 / 2 : ℝ) := by
        rw [hDsrc]
        change _ = (((F k).connection (t k)).scalarCurvature (f k x) / Q k) ^ (-1 / 2 : ℝ)
        rw [← hconnection, show A.connection.scalarCurvature (f k x) / Q k =
          (Q k)⁻¹ * A.connection.scalarCurvature (f k x) by ring,
          Real.mul_rpow (inv_nonneg.mpr (hQ k).le) hrawpos.le,
          Real.inv_rpow (hQ k).le, neg_div, Real.rpow_neg (hQ k).le,
          inv_inv, Real.sqrt_eq_rpow]
      have hsourcePow : ((Dsrc k).scalarCurvature (f k x)) ^ (-1 / 2 : ℝ) ≤
          2 * r ^ (-1 / 2 : ℝ) := by
        calc
          _ ≤ (r / 4) ^ (-1 / 2 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
          _ = _ := by
            rw [Real.div_rpow hrpos.le (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num [neg_div, Real.rpow_neg, ← Real.sqrt_eq_rpow]
            ring
      have hRpow : 0 < r ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hrpos _
      have hradius : (2 * Real.sqrt (Q k)) *
          (C * A.connection.scalarCurvature (f k x) ^ (-1 / 2 : ℝ)) ≤
            8 * d * r ^ (-1 / 2 : ℝ) := by
        calc
          _ = 2 * C * ((Dsrc k).scalarCurvature (f k x)) ^ (-1 / 2 : ℝ) := by
            rw [← hpow]
            ring
          _ ≤ 4 * C * r ^ (-1 / 2 : ℝ) := by
            calc
              _ ≤ (2 * C) * (2 * r ^ (-1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hsourcePow (by positivity)
              _ = _ := by ring
          _ ≤ 8 * d * r ^ (-1 / 2 : ℝ) := by rw [hdC]; nlinarith
      obtain ⟨y, hy, heq⟩ := hcap (N.central_sphere_subset N.center_on_central_sphere)
      have hinv : e.symm N.center = y := (congrArg e.symm heq).symm.trans
        (e.left_inv (hsource.symm ▸ hKU hy))
      have hcenterErr := abs_lt.mp (herror y hy)
      have hfy : f k y = N.center := he ▸ heq
      rw [hfy, ← hinv, ← hVcenter] at hcenterErr
      have htargetLow : r / (4 * d) ≤ D.scalarCurvature V.center := by
        rw [haquarter] at hbounds
        linarith [hbounds.1]
      have htargetUp : D.scalarCurvature V.center ≤ 4 * d * r := by
        have hbEq : b = 2 * d * r := rfl
        have hdr : r ≤ d * r := by nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hd)]
        linarith [hbounds.2]
      have htargetPos := hquarter.trans_le htargetLow
      have hVsq : V.scale ^ 2 = (D.scalarCurvature V.center)⁻¹ := by
        rw [V.scale_eq_scalar, hVconn, ← Real.rpow_mul_natCast htargetPos.le (-1 / 2) 2]
        norm_num [Real.rpow_neg_one]
      apply Or.inr
      refine ⟨V, W, hVeps, hVconn, hWopen, hWcompact, hxW, hxNot, hfront, hoverlap, ?_, ?_, ?_⟩
      · intro z hz
        exact (hWball hz).trans_le (ENNReal.ofReal_le_ofReal hradius)
      · rw [hVsq]
        exact inv_anti₀ htargetPos htargetUp
      · rw [hVsq]
        have hh := inv_anti₀ hquarter htargetLow
        simpa only [inv_div] using hh
    | component A hxA =>
      exfalso
      apply hcompact
      have hcapA : A.carrier ⊆ e '' K := by
        intro z hz
        rw [he]
        exact hball (shape_scaled_ball ((F k).metric (t k)) (hQ k)
          A.constant_pos hhighRaw hcapRadius (shape_component_distance A hxA z hz))
      let : LocallyConnectedSpace ((F k).slice (t k)).carrier :=
        ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
      have hopen : IsOpen A.carrier := by rw [A.component_eq]; exact isOpen_connectedComponent
      exact shape_compact_target e A.compact hopen ⟨f k x, hxA⟩ (hcapA.trans himageTarget)
    | round A hxA =>
      exfalso
      apply hcompact
      have haccuracy := hRound _ ((F k).metric (t k)) ((F k).connection (t k))
        epsilon A (hepsilon0.trans (min_le_left _ _)) (f k x) hxA
      have hround := round_component_subset_normalized_ball ((F k).metric (t k))
        ((F k).connection (t k)) A hepsHalf.le (hQ k) hxA hhighRaw haccuracy
      have hcapA : A.carrier ⊆ e '' K := by
        intro z hz
        rw [he]
        exact hball ((hround hz).trans_le (ENNReal.ofReal_le_ofReal hroundRadius.le))
      have hopen : IsOpen A.carrier := A.forward_image ▸ A.forward_openEmbedding.isOpen_range
      exact shape_compact_target e A.compact hopen ⟨f k x, hxA⟩ (hcapA.trans himageTarget)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp htail
  have hshift (k : ℕ) := hN0 (k + N0) (Nat.le_add_left N0 k)
  choose e hsource he N heps hcap hbounds hresult using hshift
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
  have hnorm := eventually_inverse_tangent_bound_of_finite_chart_jets g (fun k => h (k + N0)) e K
    (fun k => (hsource k).symm ▸ hKU) q L hL htarget hcover (fun i => hjets' i 0 (Nat.zero_le _))
  obtain ⟨k, ⟨V, hVeps, hVcenter, hVconn, hVcoord⟩, hk⟩ := (htransfer.and hnorm).exists
  rcases hresult k V hVeps hVconn hVcenter hVcoord hk with hn | hc
  · exact Or.inl hn
  · exact Or.inr (Or.inl hc)

end PoincareConjecture.M30
