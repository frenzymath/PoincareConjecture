import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicEquation
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfileBase
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRegularity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzArea
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionIntegrability
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.AreaDensityProduct













set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]




def m64AnnulusInterior : Set LoopPlane :=
  (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' (Set.pi Set.univ
    (fun i : Fin 2 => Set.Ioo ((0 : Fin 2 → ℝ) i)
      (![curvePeriod, 1] i)))




theorem isOpen_m64AnnulusInterior : IsOpen m64AnnulusInterior := by
  apply (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage
  exact PiLp.continuous_ofLp 2 _




theorem m64AnnulusDomain_ae_eq_interior :
    m64AnnulusDomain =ᵐ[volume] m64AnnulusInterior := by
  exact m64AnnulusDomain_ae_eq_boxInterior





theorem m64Annulus_of_lipschitz
    (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (f : LoopPlane → M)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x : ℝ, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, f (annulusPoint x 1) = c1 x)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    {zeta : ℝ}
    (harea : (∫ z in m64AnnulusDomain, m60AreaDensity g f z) < zeta) :
    ∃ A : M64Annulus g c0 c1, A.map = f ∧ A.area < zeta := by
  let S := m64AnnulusInterior
  have hS : IsOpen S := isOpen_m64AnnulusInterior
  have hSsub : S ⊆ m64AnnulusDomain := by
    intro x hx
    simp only [S, m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo] at hx
    change 0 ≤ x 0 ∧ x 0 ≤ curvePeriod ∧ 0 ≤ x 1 ∧ x 1 ≤ 1
    have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simpa using ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  have hLipS : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
    intro x hx y hy
    exact hLip ⟨x, hSsub hx⟩ ⟨y, hSsub hy⟩
  have hDiffS := m60_ae_mdifferentiable_of_metric_lipschitzOn g hS hL hLipS
  have hDiff : ∀ᵐ z ∂volume,
      z ∈ m64AnnulusDomain → MDifferentiableAt (𝓡 2) (𝓡 n) f z := by
    filter_upwards [hDiffS, m64AnnulusDomain_ae_eq_interior] with z hz hzi
    intro hzdom
    exact hz (hzi.mp hzdom)
  have hIntS := m60AreaIntegral_bound_of_metric_lipschitzOn g hS hfinite hL hLipS
  have hInt : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume := by
    exact (integrableOn_congr_set_ae m64AnnulusDomain_ae_eq_interior).mpr hIntS.1
  let A : M64Annulus g c0 c1 := {
    map := f
    continuous_on_domain := hcontinuous
    periodic := hperiodic
    lower_boundary := hlower
    upper_boundary := hupper
    lipschitz_constant := L
    lipschitz_nonnegative := hL
    lipschitz_on_domain := hLip
    ae_manifold_differentiable := hDiff
    area_integrable := hInt }
  refine ⟨A, rfl, ?_⟩
  exact harea

omit [T2Space M] in



theorem m64PiecewiseC1Annulus_of_cuts
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {k : ℕ} (hk : 0 < k)
    (cut : Fin (k + 1) → ℝ) (hcut : StrictMono cut)
    (hcut_zero : cut 0 = 0)
    (hcut_last : cut (Fin.last k) = curvePeriod)
    (hmdiff : ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map
      {p | cut j.castSucc <= p 0 ∧ p 0 <= cut j.succ ∧
        0 <= p 1 ∧ p 1 <= 1}) :
    M64PiecewiseC1Annulus A := by
  exact ⟨k, hk, cut, hcut, hcut_zero, hcut_last, hmdiff⟩

omit [T2Space M] in



theorem m64GeodesicAnnulus_of_sides
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (side : ∀ x : ℝ,
      M63MinimizingGeodesicSide g D 1 (c0 x) (c1 x))
    (hmap : ∀ x s : ℝ,
      A.map (annulusPoint x s) = (side x).map s) :
    M64GeodesicAnnulus D A := by
  intro x
  exact ⟨side x, fun s _ => hmap x s⟩




theorem m64AnnulusWitness_of_lipschitz
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {c0 c1 : ℝ → M} (f : LoopPlane → M)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x : ℝ, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, f (annulusPoint x 1) = c1 x)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    {zeta : ℝ}
    (harea : (∫ z in m64AnnulusDomain, m60AreaDensity g f z) < zeta)
    {k : ℕ} (hk : 0 < k) (cut : Fin (k + 1) → ℝ)
    (hcut : StrictMono cut) (hcut_zero : cut 0 = 0)
    (hcut_last : cut (Fin.last k) = curvePeriod)
    (hmdiff : ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 f
      {p | cut j.castSucc <= p 0 ∧ p 0 <= cut j.succ ∧
        0 <= p 1 ∧ p 1 <= 1})
    (side : ∀ x : ℝ,
      M63MinimizingGeodesicSide g D 1 (c0 x) (c1 x))
    (hmap : ∀ x s : ℝ,
      f (annulusPoint x s) = (side x).map s) :
    ∃ A : M64Annulus g c0 c1,
      M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
        0 ≤ A.area ∧ A.area < zeta := by
  obtain ⟨A, hAmap, hAarea⟩ := m64Annulus_of_lipschitz g f hcontinuous hperiodic
    hlower hupper hL hLip hfinite harea
  have hnonneg : 0 ≤ A.area := by
    unfold M64Annulus.area m64AnnulusArea
    exact integral_nonneg (fun _ => m60AreaDensity_nonneg g A.map _)
  refine ⟨A, m64PiecewiseC1Annulus_of_cuts A hk cut hcut hcut_zero
    hcut_last (by simpa [hAmap] using hmdiff),
    m64GeodesicAnnulus_of_sides A side (by simpa [hAmap] using hmap), hnonneg,
    hAarea⟩

omit [T2Space M] in




theorem exists_m63MinimizingGeodesicSide_of_interpolator
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {p q : M} {r : ℝ} {H : ℝ × (M × M) → M}
    (hr : g.edist p q < ENNReal.ofReal r)
    (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun t : ℝ => H (t, p, q)) (Ioo (-1 : ℝ) 2))
    (hprops : g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q) :
    Nonempty (M63MinimizingGeodesicSide g D 1 p q) := by
  rcases hprops hr with ⟨h0, h1, hgeo, hspeed, hlength⟩
  refine ⟨{
    map := fun t => H (t, p, q)
    domain := Ioo (-1 : ℝ) 2
    domain_open := isOpen_Ioo
    interval_subset := ?_
    smooth := hsmooth
    start := h0
    finish := h1
    speed := (g.edist p q).toReal
    speed_nonnegative := ENNReal.toReal_nonneg
    constant_speed := ?_
    equation := ?_
    minimizing := hlength }⟩
  · intro t ht
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    have hIoo : t ∈ Ioo (-1 : ℝ) 2 := by
      constructor <;> linarith [ht.1, ht.2]
    exact hspeed t hIoo
  · intro t ht
    exact hgeo.pullback_velocity_eq_zero D ht

omit [T2Space M] [IsManifold (𝓡 n) ∞ M] in



theorem contMDiffOn_interpolator_slice
    {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    {p q : M} (hpq : (p, q) ∈ U) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun t : ℝ => H (t, p, q)) (Ioo (-1 : ℝ) 2) := by
  let i : ℝ → ℝ × (M × M) := fun t => (t, (p, q))
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun _ : ℝ => p) (Ioo (-1 : ℝ) 2) := contMDiffOn_const
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun _ : ℝ => q) (Ioo (-1 : ℝ) 2) := contMDiffOn_const
  have hi : ContMDiffOn 𝓘(ℝ, ℝ)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) ∞ i
      (Ioo (-1 : ℝ) 2) := by
    exact contMDiffOn_id.prodMk (hp.prodMk hq)
  have himage : Ioo (-1 : ℝ) 2 ⊆ i ⁻¹' (Ioo (-1 : ℝ) 2 ×ˢ U) := by
    intro t ht
    exact ⟨ht, hpq⟩
  have hc := hH.comp hi himage
  simpa only [i, Function.comp_def] using hc

omit [T2Space M] [IsManifold (𝓡 n) ∞ M] in



theorem m64_contMDiffOn_interpolator_strip
    {U : Set (M × M)} {V : Set ℝ} {H : ℝ × (M × M) → M}
    {gamma side upper : ℝ → M} {left : ℝ} {S : Set LoopPlane}
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hside : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ side V)
    (htime : ∀ p ∈ S, p 1 ∈ Ioo (-1 : ℝ) 2)
    (hleft : ∀ p ∈ S, p 0 - left ∈ V)
    (hpair : ∀ p ∈ S, (gamma (p 0), side (p 0 - left)) ∈ U)
    (hupper : ∀ p ∈ S, upper (p 0) = side (p 0 - left)) :
    ContMDiffOn (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => H (p 1, gamma (p 0), upper (p 0))) S := by
  let p0 : LoopPlane → ℝ := fun p => p 0
  let p1 : LoopPlane → ℝ := fun p => p 1
  have hp0 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) 1 p0 Set.univ := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffOn
  have hp1 : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) 1 p1 Set.univ := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
      (n := ∞) |>.of_le (m := 1) (by norm_num) |>.contMDiff.contMDiffOn
  have hp0top : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ p0 Set.univ := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
      (n := ∞) |>.contMDiff.contMDiffOn
  have hp0S := hp0.mono (subset_univ S)
  have hp1S := hp1.mono (subset_univ S)
  have hgammaS : ContMDiffOn (𝓡 2) (𝓡 n) 1
      (fun p => gamma (p 0)) S := by
    have hc := hgamma.comp hp0S (fun _ _ => mem_univ _)
    simpa only [p0, Function.comp_def] using hc
  let phi : LoopPlane → ℝ := fun p => p 0 - left
  have hphi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ phi Set.univ := by
    have hc := hp0top.add (contMDiffOn_const :
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun _ : LoopPlane => -left) Set.univ)
    change ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p => p0 p + -left) Set.univ at hc
    simpa only [phi, sub_eq_add_neg] using hc
  have hphiS := hphi.mono (subset_univ S)
  have hsideS : ContMDiffOn (𝓡 2) (𝓡 n) 1
      (fun p => side (p 0 - left)) S := by
    have hc := hside.comp hphiS (fun p hp => hleft p hp)
    have hc1 := hc.of_le (m := 1) (by norm_num)
    simpa only [phi, p0, Function.comp_def] using hc1
  have hpairmap : ContMDiffOn (𝓡 2) ((𝓡 n).prod (𝓡 n)) 1
      (fun p => (gamma (p 0), side (p 0 - left))) S :=
    hgammaS.prodMk hsideS
  have hinput : ContMDiffOn (𝓡 2)
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) 1
      (fun p => (p 1, (gamma (p 0), side (p 0 - left)))) S :=
    hp1S.prodMk hpairmap
  have himage : S ⊆ (fun p : LoopPlane =>
      (p 1, (gamma (p 0), side (p 0 - left)))) ⁻¹'
      (Ioo (-1 : ℝ) 2 ×ˢ U) := by
    intro p hp
    exact ⟨htime p hp, hpair p hp⟩
  have hH1 := hH.of_le (m := 1) (by norm_num)
  have hc := hH1.comp hinput himage
  have hcomp : ContMDiffOn (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => H (p 1, gamma (p 0), side (p 0 - left))) S := by
    simpa only [Function.comp_def] using hc
  exact hcomp.congr (fun p hp =>
    congrArg (fun q => H (p 1, gamma (p 0), q)) (hupper p hp))




noncomputable def m64PolygonCut (N : ℕ) : Fin (N + 1) → ℝ :=
  fun j => (j.val : ℝ) * m63CellLength N




theorem m64PolygonCut_strictMono {N : ℕ} (hN : 0 < N) :
    StrictMono (m64PolygonCut N) := by
  intro i j hij
  have hval : i.val < j.val := hij
  have hreal : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hval
  dsimp [m64PolygonCut]
  exact mul_lt_mul_of_pos_right hreal (m63CellLength_pos hN)




theorem m64PolygonCut_zero {N : ℕ} : m64PolygonCut N 0 = 0 := by
  simp [m64PolygonCut]




theorem m64PolygonCut_last {N : ℕ} (hN : 0 < N) :
    m64PolygonCut N (Fin.last N) = curvePeriod := by
  simp only [m64PolygonCut, Fin.val_last]
  exact m63_count_mul_cellLength hN




noncomputable def m64PolygonCellSet {N : ℕ} (j : Fin N) : Set LoopPlane :=
  {p | m63CellLeft N j ≤ p 0 ∧ p 0 ≤ m63CellLeft N j + m63CellLength N ∧
    0 ≤ p 1 ∧ p 1 ≤ 1}

omit [T2Space M] in



theorem m64_polygon_cell_contMDiffOn
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U) :
    ∀ j : Fin N, ContMDiffOn (𝓡 2) (𝓡 n) 1
      (fun p : LoopPlane => H (p 1, gamma (p 0), polygon.map (p 0)))
      (m64PolygonCellSet j) := by
  intro j
  let S := m64PolygonCellSet j
  have htime : ∀ p ∈ S, p 1 ∈ Ioo (-1 : ℝ) 2 := by
    intro p hp
    exact ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩
  have hleft : ∀ p ∈ S, p 0 - m63CellLeft N j ∈
      (polygon.side j).domain := by
    intro p hp
    apply (polygon.side j).interval_subset
    constructor <;> linarith [hp.1, hp.2.1]
  have hpair' : ∀ p ∈ S,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U := by
    exact hpair j
  have hupper : ∀ p ∈ S,
      polygon.map (p 0) = (polygon.side j).map
        (p 0 - m63CellLeft N j) := by
    intro p hp
    have hs : p 0 - m63CellLeft N j ∈
        Icc (0 : ℝ) (m63CellLength N) := by
      constructor <;> linarith [hp.1, hp.2.1]
    have hc := polygon.cell_agreement j _ hs
    convert hc using 1
    ring_nf
  exact m64_contMDiffOn_interpolator_strip hH hgamma
    (polygon.side j).smooth htime hleft hpair' hupper







theorem m64PolygonCut_cellSet {N : ℕ} (j : Fin N) :
    {p : LoopPlane |
      m64PolygonCut N j.castSucc ≤ p 0 ∧
      p 0 ≤ m64PolygonCut N j.succ ∧
      0 ≤ p 1 ∧ p 1 ≤ 1} = m64PolygonCellSet j := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hleft, hright, h0, h1⟩
    dsimp [m64PolygonCut] at hleft hright
    dsimp [m64PolygonCellSet]
    have hright' : p 0 ≤ m63CellLeft N j + m63CellLength N := by
      simpa only [m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hright
    exact ⟨hleft, hright', h0, h1⟩
  · intro hp
    rcases hp with ⟨hleft, hright, h0, h1⟩
    dsimp [m64PolygonCut]
    dsimp [m64PolygonCellSet] at hleft hright
    have hright' : p 0 ≤ (↑(j.val + 1) : ℝ) * m63CellLength N := by
      simpa only [m63CellLeft, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hright
    exact ⟨hleft, hright', h0, h1⟩

omit [T2Space M] in



theorem m64_polygon_piecewiseC1_of_interpolator
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N)
    (polygon : M63GeodesicPolygon g D N)
    {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hmap : A.map = (fun p : LoopPlane =>
      H (p 1, gamma (p 0), polygon.map (p 0))))
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U) :
    M64PiecewiseC1Annulus A := by
  apply m64PiecewiseC1Annulus_of_cuts A hN (m64PolygonCut N)
    (m64PolygonCut_strictMono hN) m64PolygonCut_zero
    (m64PolygonCut_last hN)
  intro j
  rw [hmap, m64PolygonCut_cellSet]
  exact m64_polygon_cell_contMDiffOn polygon hH hgamma hpair j



omit [T2Space M] in



theorem m64AnnulusIntegral_le_of_ae_column_bounds
    {g : RiemannianMetric n M} {f : LoopPlane → M}
    {K0 K1 : ℝ} (hK0 : 0 ≤ K0)
    (hfinite : volume m64AnnulusDomain ≠ (⊤ : ENNReal))
    (hInt : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume)
    (hcol0 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ K0)
    (hcol1 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1) :
    (∫ z in m64AnnulusDomain, m60AreaDensity g f z) ≤
      K0 * K1 * volume.real m64AnnulusDomain := by
  apply m64AnnulusIntegral_le_of_ae_density_bound hfinite hInt
  filter_upwards [hcol0, hcol1] with z hz0 hz1
  have h1 : 0 ≤ g.tangentNorm (f z)
      (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
    Real.sqrt_nonneg _
  exact (m60AreaDensity_le_tangentNorm_product g f z).trans
    (mul_le_mul hz0 hz1 h1 hK0)




theorem m64AnnulusIntegral_le_of_lipschitzOn_and_ae_column_bounds
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    {L K0 K1 : ℝ} (hL : 0 ≤ L) (hK0 : 0 ≤ K0)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    (hcol0 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ K0)
    (hcol1 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1) :
    (∫ z in m64AnnulusDomain, m60AreaDensity g f z) ≤
      K0 * K1 * volume.real m64AnnulusDomain := by
  let S := m64AnnulusInterior
  have hS : IsOpen S := isOpen_m64AnnulusInterior
  have hSsub : S ⊆ m64AnnulusDomain := by
    intro x hx
    simp only [S, m64AnnulusInterior, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, Set.mem_Ioo] at hx
    change 0 ≤ x 0 ∧ x 0 ≤ curvePeriod ∧ 0 ≤ x 1 ∧ x 1 ≤ 1
    have h0 := hx 0 trivial
    have h1 := hx 1 trivial
    simpa using ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩
  have hLipS : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤ ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
    intro x hx y hy
    exact hLip ⟨x, hSsub hx⟩ ⟨y, hSsub hy⟩
  have hIntS := m60AreaIntegral_bound_of_metric_lipschitzOn g hS hfinite hL hLipS
  have hInt : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume := by
    exact (integrableOn_congr_set_ae m64AnnulusDomain_ae_eq_interior).mpr hIntS.1
  have hmeasure : volume m64AnnulusDomain = volume m64AnnulusInterior :=
    measure_congr m64AnnulusDomain_ae_eq_interior
  refine m64AnnulusIntegral_le_of_ae_column_bounds hK0 ?_ hInt hcol0 hcol1
  rw [hmeasure]
  exact hfinite




theorem m64AnnulusWitness_of_lipschitz_columns
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {c0 c1 : ℝ → M} (f : LoopPlane → M)
    (hcontinuous : ContinuousOn f m64AnnulusDomain)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x : ℝ, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, f (annulusPoint x 1) = c1 x)
    {L K0 K1 : ℝ} (hL : 0 ≤ L) (hK0 : 0 ≤ K0)
    (hLip : ∀ x y : m64AnnulusDomain,
      g.edist (f x) (f y) ≤
        ENNReal.ofReal L * ENNReal.ofReal ‖(x : LoopPlane) - y‖)
    (hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal))
    (hcol0 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ K0)
    (hcol1 : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ K1)
    {zeta : ℝ}
    (hstrict : K0 * K1 * volume.real m64AnnulusDomain < zeta)
    {k : ℕ} (hk : 0 < k) (cut : Fin (k + 1) → ℝ)
    (hcut : StrictMono cut) (hcut_zero : cut 0 = 0)
    (hcut_last : cut (Fin.last k) = curvePeriod)
    (hmdiff : ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 f
      {p | cut j.castSucc <= p 0 ∧ p 0 <= cut j.succ ∧
        0 <= p 1 ∧ p 1 <= 1})
    (side : ∀ x : ℝ,
      M63MinimizingGeodesicSide g D 1 (c0 x) (c1 x))
    (hmap : ∀ x s : ℝ,
      f (annulusPoint x s) = (side x).map s) :
    ∃ A : M64Annulus g c0 c1,
      M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
        0 ≤ A.area ∧ A.area < zeta := by
  have harea_le := m64AnnulusIntegral_le_of_lipschitzOn_and_ae_column_bounds
    g hL hK0 hLip hfinite hcol0 hcol1
  have harea : (∫ z in m64AnnulusDomain, m60AreaDensity g f z) < zeta :=
    harea_le.trans_lt hstrict
  exact m64AnnulusWitness_of_lipschitz g D f hcontinuous hperiodic hlower hupper
    hL hLip hfinite harea hk cut hcut hcut_zero hcut_last hmdiff side hmap

end PoincareConjecture
