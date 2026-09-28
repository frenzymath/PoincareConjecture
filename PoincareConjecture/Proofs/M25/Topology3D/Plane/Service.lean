import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ConvexExterior
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedCurveTransfer
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialCurveAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TriangleCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedRadialDirection
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedProfileChoice
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CircleBoundaryAssembly
import PoincareConjecture.Proofs.M25.Topology3D.Plane.FamilyPersistence

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem nonempty_planarSchoenfliesData_of_diffeomorph
    (c : UnitCircle → E2) (F : E2 ≃ₘ[ℝ] E2)
    (hboundary : ∀ q : UnitCircle, F q.1 = c q) :
    Nonempty (PlanarSchoenfliesData c) := by
  have hrange : F '' sphere (0 : E2) 1 = range c := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hboundary ⟨x, hx⟩).symm⟩
    · rintro y ⟨q, rfl⟩
      exact ⟨q.1, q.2, hboundary q⟩
  have hdisj : Disjoint (F '' ball (0 : E2) 1) (range c) := by
    rw [← hrange]
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨v, hv, hvx⟩
    have he : v = x := F.toEquiv.injective hvx
    subst v
    exact Set.disjoint_left.mp sphere_disjoint_ball hv hx
  have hbounded : Bornology.IsBounded (F '' ball (0 : E2) 1) :=
    ((isCompact_closedBall (0 : E2) 1).image F.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have hrank : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  have hout : univ \ (F '' ball (0 : E2) 1 ∪ range c) =
      F '' (closedBall (0 : E2) 1)ᶜ := by
    rw [← hrange, ← image_union, ball_union_sphere]
    simpa only [sdiff_eq_compl_inter, inter_univ, Diffeomorph.coe_toHomeomorph] using
      (F.toHomeomorph.image_compl (closedBall (0 : E2) 1)).symm
  refine ⟨{
    inside := F '' ball 0 1
    inside_open := F.toHomeomorph.isOpenMap _ isOpen_ball
    inside_bounded := hbounded
    inside_connected := (isConnected_ball zero_lt_one).image F F.continuous.continuousOn
    outside_connected := ?_
    inside_disjoint := hdisj
    radius := 2
    one_lt_radius := by norm_num
    chart := F
    chart_smooth := F.contDiff.contDiffOn
    chart_injOn := F.toEquiv.injective.injOn
    chart_open_map := F.toHomeomorph.isOpenMap _ isOpen_ball
    chart_image_inside := rfl
    chart_boundary := hboundary
    chart_inverse := ⟨F.symm, F.symm.contDiff.contDiffOn,
      fun x _ => F.symm_apply_apply x⟩ }⟩
  rw [hout]
  exact (isPathConnected_compl_closedBall_of_one_lt_rank hrank (0 : E2) 1).isConnected.image
    F F.continuous.continuousOn

theorem nonempty_planarSchoenfliesFamilyData_of_diffeomorphs
    (a b : ℝ) (c : ℝ → UnitCircle → E2) (F : ℝ → (E2 ≃ₘ[ℝ] E2))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2))
    (hboundary : ∀ z ∈ Icc a b, ∀ q : UnitCircle, F z q.1 = c z q) :
    Nonempty (PlanarSchoenfliesFamilyData c a b) := by
  have himm (z : ℝ) (x : E2) : Injective (fderiv ℝ (F z) x) := by
    have hcomp : (fun y : E2 => (F z).symm (F z y)) = id :=
      funext fun y => (F z).symm_apply_apply y
    have hder := fderiv_comp x
      ((F z).symm.contDiff.differentiable (by simp)).differentiableAt
      ((F z).contDiff.differentiable (by simp)).differentiableAt
    have hid : (fderiv ℝ (F z).symm (F z x)).comp (fderiv ℝ (F z) x) =
        ContinuousLinearMap.id ℝ E2 := by
      rw [← hder]
      change fderiv ℝ (fun y : E2 => (F z).symm (F z y)) x = _
      rw [hcomp, fderiv_id]
    intro u v huv
    have h := congrArg (fderiv ℝ (F z).symm (F z x)) huv
    have hu := congrArg (fun L : E2 →L[ℝ] E2 => L u) hid
    have hv := congrArg (fun L : E2 →L[ℝ] E2 => L v) hid
    exact hu.symm.trans (h.trans hv)
  refine ⟨{
    radius := 2
    one_lt_radius := by norm_num
    margin := 1
    margin_pos := zero_lt_one
    chart := fun z x => F z x
    chart_smooth := hF.contDiffOn
    chart_injOn := fun z _ => (F z).toEquiv.injective.injOn
    chart_immersion := fun z _ x _ => himm z x
    chart_boundary := hboundary
    chart_inside := ?_ }⟩
  intro z hz
  refine ⟨(F z).toHomeomorph.isOpenMap _ isOpen_ball, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨q, hq⟩
    have h : F z q.1 = F z x := (hboundary z hz q).trans hq
    have he := (F z).toEquiv.injective h
    have hmem : x ∈ sphere (0 : E2) 1 := he ▸ q.2
    exact Set.disjoint_left.mp sphere_disjoint_ball hmem hx
  · exact ((isCompact_closedBall (0 : E2) 1).image (F z).continuous).isBounded.subset
      (image_mono ball_subset_closedBall)

theorem exists_planar_curve_ambient_diffeomorph (c : UnitCircle → E2)
    (hc : IsPlanarEmbedding c) :
    ∃ Φ : E2 ≃ₘ[ℝ] E2, ∀ q : UnitCircle, Φ q.1 = c q := by
  let : Fact (Module.finrank ℝ E2 = 2) := ⟨by simp [E2]⟩
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  let o : Orientation ℝ E2 (Fin 2) :=
    (Complex.basisOneI.map e.toLinearEquiv).orientation
  let q0 : UnitCircle := sphereCircleParameter e 0
  let c0 : ℝ → UnitCircle → E2 := fun _ => c
  have hc0 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c0 p.1 p.2) := hc.1.comp contMDiff_snd
  obtain ⟨m, hm, n, hn, hdata⟩ := exists_rounded_inscribed_curve_transport e o q0 c0 hc0
    (a := 0) (b := 1) (ε := 1) zero_le_one zero_lt_one
    (fun _ _ => hc.2.1) (fun _ _ => hc.2.2)
  let : NeZero n := ⟨by omega⟩
  let h : ℝ := 2 * Real.pi / n
  let p : Polygon E2 n := inscribedPolygon (fun t => c (sphereCircleParameter e t))
    (fun i : Fin (n + 1) => h * (i.val : ℝ))
  change 0 < h ∧ h < 1 ∧
    (∀ z ∈ Icc (0 - m / 2) (1 + m / 2), IsSimplePolygon p) ∧ _ at hdata
  obtain ⟨_, _, hsimple, hsampling⟩ := hdata
  have hp : IsSimplePolygon p := hsimple 0 ⟨by linarith, by linarith⟩
  obtain ⟨P, hP, hP0, hPsimple, b, _, hdet⟩ :=
    hp.exists_smooth_triangle_motion (by simp [E2])
  obtain ⟨C, hC⟩ := exists_triangle_coordinate_diffeomorph b
  let q : Polygon ℂ n := ⟨fun i => triangleComplexAffineMap b (P 1 i)⟩
  have hqdet (i : Fin n) : 0 < complexEdgeDet (q i) (q (finRotate n i)) := by
    simpa only [q, complexEdgeDet, triangleComplexAffineMap_apply, triangleEdgeDet]
      using hdet i
  obtain ⟨d1, hd1, hangular⟩ := exists_roundedPolygon_det_threshold q hqdet
  obtain ⟨d0, hd0, hdquarter, hprofile⟩ := exists_rounded_polygon_family_threshold
    isCompact_Icc P hP hPsimple zero_lt_one
  let δ := min d0 d1 / 2
  have hδ : 0 < δ := half_pos (lt_min hd0 hd1)
  have hδ0 : δ < d0 := by dsimp [δ]; linarith [min_le_left d0 d1]
  have hδ1 : δ < d1 := by dsimp [δ]; linarith [min_le_right d0 d1]
  have hδhalf : δ < 1 / 2 := by linarith
  obtain ⟨ρ, hρ, _, _, htail, hbound, hder⟩ := exists_smooth_absolute_rounding hδ
  obtain ⟨hG, hGper, hGi, hGd, _⟩ := hprofile δ hδ hδ0 ρ hρ htail hbound hder
  let G : ℝ → ℝ → E2 := fun z => roundedPolygonParameter ρ (P z)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let k : ℝ → UnitCircle → E2 := fun z => periodicCircleCurve (n : ℝ) e (G z)
  have hk : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun x : ℝ × UnitCircle => k x.1 x.2) :=
    contMDiff_periodicCircleCurve_family hnpos e G hG hGper
  obtain ⟨F, _, _, _, _, _, hFrange⟩ := exists_supported_curve_family_transport e o q0 k hk
    (a := 0) (b := 1) zero_lt_one
    (fun z hz => injective_periodicCircleCurve hnpos e (hGper z) (hGi z hz))
    (fun z hz => mfderiv_periodicCircleCurve_injective hnpos e (hGper z)
      (hG.comp (contDiff_const.prodMk contDiff_id)) (hGd z hz))
  have hmid : F 1 '' range (roundedPolygonParameter ρ p) = range (G 1) := by
    have hh := hFrange 1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    rw [range_comp'] at hh
    change F 1 '' range (periodicCircleCurve (n : ℝ) e (G 0)) =
      range (periodicCircleCurve (n : ℝ) e (G 1)) at hh
    rw [range_periodicCircleCurve hnpos e (hGper 0),
      range_periodicCircleCurve hnpos e (hGper 1)] at hh
    simpa only [G, hP0] using hh
  obtain ⟨S, _, _, _, _, hSrange⟩ := hsampling δ hδ hδhalf ρ hρ htail hbound hder
  have hstart : S 0 '' range c = range (roundedPolygonParameter ρ p) := by
    have hh := hSrange 0 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    rw [range_comp'] at hh
    exact hh
  let γ : ℝ → ℂ := fun t => C (G 1 t)
  have hγ : ContDiff ℝ ∞ γ := C.contDiff.comp
    (hG.comp (contDiff_const.prodMk contDiff_id))
  have hγeq : γ = roundedPolygonParameter ρ q := by
    funext t
    rw [show γ t = triangleComplexAffineMap b (G 1 t) from hC _]
    exact triangleComplexAffineMap_roundedPolygon b ρ (P 1) t
  have hγangular (t : ℝ) : 0 < complexEdgeDet (γ t) (deriv γ t) := by
    rw [hγeq]
    exact hangular δ hδ hδ1 ρ (hρ.differentiable (by simp)) htail hbound hder t
  have hγper : Periodic γ (n : ℝ) := fun t => congrArg C (hGper 1 t)
  have hγi : InjOn γ (Ico 0 (n : ℝ)) := by
    intro s hs t ht heq
    exact hGi 1 ⟨zero_le_one, le_rfl⟩ hs ht (C.toEquiv.injective heq)
  obtain ⟨B, r, hB, hr, hBd, hrpos, hrper, hBper, hrepr, hri⟩ :=
    exists_positive_polar_representation γ hγ hγangular hγper hγi
  let ei := LinearIsometryEquiv.refl ℝ ℂ
  let : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  obtain ⟨R, hR⟩ := exists_radial_curve_ambient_straightening ei Complex.orientation
    (sphereCircleParameter ei 0) hnpos B r hB hr hBd hrpos hrper hBper hri
  have hRγ : R '' range γ = sphere (0 : ℂ) 1 := by
    rw [show γ = (fun t => r t • (sphereCircleParameter ei (B t) : ℂ)) from funext hrepr]
    exact hR
  let E := e.toContinuousLinearEquiv.toDiffeomorph
  have heunit : E '' sphere (0 : ℂ) 1 = sphere (0 : E2) 1 := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      change e z ∈ sphere (0 : E2) 1
      rw [mem_sphere_zero_iff_norm, e.norm_map]
      exact mem_sphere_zero_iff_norm.mp hz
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [mem_sphere_zero_iff_norm, e.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp hx
  let D : E2 ≃ₘ[ℝ] E2 := (((S 0).trans (F 1)).trans C).trans (R.trans E)
  have hDrange : D '' range c = sphere (0 : E2) 1 := by
    have hCrange : C '' range (G 1) = range γ := (range_comp' C (G 1)).symm
    calc
      D '' range c = E '' (R '' (C '' (F 1 '' (S 0 '' range c)))) := by
        simp only [image_image]
        rfl
      _ = sphere (0 : E2) 1 := by rw [hstart, hmid, hCrange, hRγ, heunit]
  let U : ℝ × ℝ → E2 := fun x => D (c (sphereCircleParameter e x.2))
  have hU : ContDiff ℝ ∞ U := D.contDiff.comp
    (contDiff_curveFamily_circleParameter e c0 hc0)
  have hUnorm (x : ℝ × ℝ) : ‖U x‖ = 1 := mem_sphere_zero_iff_norm.mp
    (hDrange ▸ (show U x ∈ D '' range c from
      ⟨c (sphereCircleParameter e x.2), ⟨sphereCircleParameter e x.2, rfl⟩, rfl⟩))
  have hUper (z : ℝ) : Periodic (fun s => U (z, s)) (2 * Real.pi) := by
    intro s
    change D (c (sphereCircleParameter e (s + 2 * Real.pi))) = _
    rw [periodic_sphereCircleParameter e]
  have hUne (z s : ℝ) : deriv (fun t => U (z, t)) s ≠ 0 := by
    intro hz
    have hUs : ContDiff ℝ ∞ (fun t => U (z, t)) :=
      hU.comp (contDiff_const.prodMk contDiff_id)
    have hd := (D.symm.contDiff.differentiable (by simp) (U (z, s))).hasFDerivAt.comp_hasDerivAt
      s ((hUs.differentiable (by simp) s).hasDerivAt)
    have heq : (D.symm : E2 → E2) ∘ (fun t => U (z, t)) =
        (fun t => c (sphereCircleParameter e t)) := by
      funext t
      exact D.symm_apply_apply _
    rw [heq, hz, map_zero] at hd
    exact deriv_curveFamily_circleParameter_ne_zero e c0 hc0 z s (hc.2.2 _) hd.deriv
  have hUi (z s t : ℝ) (hh : U (z, s) = U (z, t)) :
      sphereCircleParameter e s = sphereCircleParameter e t :=
    hc.2.1 (D.toEquiv.injective hh)
  obtain ⟨H, _, _, hH⟩ := exists_unit_curve_ambient_extension e q0 U hU hUnorm hUper hUne hUi
  refine ⟨(H 0).trans D.symm, ?_⟩
  intro q
  obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
  change D.symm (H 0 (sphereCircleParameter e s : E2)) = _
  rw [hH]
  exact D.symm_apply_apply _

theorem nonempty_planarSchoenfliesData (c : UnitCircle → E2)
    (hc : IsPlanarEmbedding c) : Nonempty (PlanarSchoenfliesData c) := by
  obtain ⟨Φ, hΦ⟩ := exists_planar_curve_ambient_diffeomorph c hc
  exact nonempty_planarSchoenfliesData_of_diffeomorph c Φ hΦ

theorem exists_planar_curve_family_ambient_diffeomorphs
    (a b : ℝ) (c : ℝ → UnitCircle → E2) (hab : a < b)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2))
    (hemb : ∀ z ∈ Icc a b, IsPlanarEmbedding (c z)) :
    ∃ Φ : ℝ → (E2 ≃ₘ[ℝ] E2),
      ContDiff ℝ ∞ (fun p : ℝ × E2 => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (Φ p.1).symm p.2) ∧
      ∀ z ∈ Icc a b, ∀ q : UnitCircle, Φ z q.1 = c z q := by
  let : Fact (Module.finrank ℝ E2 = 2) := ⟨by simp [E2]⟩
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  let o : Orientation ℝ E2 (Fin 2) :=
    (Complex.basisOneI.map e.toLinearEquiv).orientation
  let q0 : UnitCircle := sphereCircleParameter e 0
  obtain ⟨m, hm, hmargin⟩ := exists_curve_embedding_margin o q0 c hc hab.le
    (fun z hz => (hemb z hz).2.1) (fun z hz => (hemb z hz).2.2)
  let d := m / 2
  let L := a - d
  let U := b + d
  have hd : 0 < d := half_pos hm
  have hLU : L < U := by dsimp [L, U]; linarith
  have hband (z : ℝ) (hz : z ∈ Icc L U) : z ∈ Ioo (a - m) (b + m) := by
    change a - d ≤ z ∧ z ≤ b + d at hz
    dsimp [d] at hz
    constructor <;> linarith [hz.1, hz.2]
  have hbase : IsPlanarEmbedding (c L) :=
    ⟨hc.comp (contMDiff_const.prodMk contMDiff_id),
      hmargin L (hband L ⟨le_rfl, hLU.le⟩)⟩
  obtain ⟨θ, hθ, hθrange, hθid⟩ := exists_smooth_interval_clamp hab.le hd
  obtain ⟨F, hF, hFi, _, _, _, hFrange⟩ :=
    exists_supported_curve_family_transport e o q0 c hc hLU
      (fun z hz => (hmargin z (hband z hz)).1)
      (fun z hz => (hmargin z (hband z hz)).2)
  obtain ⟨Φ0, hΦ0⟩ := exists_planar_curve_ambient_diffeomorph (c L) hbase
  let A : ℝ → (E2 ≃ₘ[ℝ] E2) := fun z => Φ0.trans (F (θ z))
  have hA : ContDiff ℝ ∞ (fun p : ℝ × E2 => A p.1 p.2) :=
    hF.comp ((hθ.comp contDiff_fst).prodMk (Φ0.contDiff.comp contDiff_snd))
  have hAi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (A p.1).symm p.2) :=
    Φ0.symm.contDiff.comp
      (hFi.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))
  have hΦrange : Φ0 '' sphere (0 : E2) 1 = range (c L) := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hΦ0 ⟨x, hx⟩).symm⟩
    · rintro y ⟨q, rfl⟩
      exact ⟨q.1, q.2, hΦ0 q⟩
  have hArange (z : ℝ) : A z '' sphere (0 : E2) 1 = range (c (θ z)) := by
    calc
      A z '' sphere (0 : E2) 1 = F (θ z) '' (Φ0 '' sphere (0 : E2) 1) := by
        rw [image_image]
        rfl
      _ = range (c (θ z)) := by
        rw [hΦrange, ← range_comp']
        exact hFrange (θ z) (hθrange z)
  let γ : ℝ × ℝ → E2 := fun p =>
    (A p.1).symm (c (θ p.1) (sphereCircleParameter e p.2))
  have hγ : ContDiff ℝ ∞ γ := hAi.comp
    (contDiff_fst.prodMk ((contDiff_curveFamily_circleParameter e c hc).comp
      ((hθ.comp contDiff_fst).prodMk contDiff_snd)))
  have hγnorm (p : ℝ × ℝ) : ‖γ p‖ = 1 := by
    have hmemb : c (θ p.1) (sphereCircleParameter e p.2) ∈ A p.1 '' sphere (0 : E2) 1 := by
      rw [hArange]
      exact ⟨sphereCircleParameter e p.2, rfl⟩
    obtain ⟨x, hx, heq⟩ := hmemb
    change ‖(A p.1).symm (c (θ p.1) (sphereCircleParameter e p.2))‖ = 1
    rw [← heq, Diffeomorph.symm_apply_apply]
    exact mem_sphere_zero_iff_norm.mp hx
  have hγper (z : ℝ) : Periodic (fun s => γ (z, s)) (2 * Real.pi) := by
    intro s
    change (A z).symm (c (θ z) (sphereCircleParameter e (s + 2 * Real.pi))) = _
    rw [periodic_sphereCircleParameter e]
  have hγne (z s : ℝ) : deriv (fun t => γ (z, t)) s ≠ 0 := by
    intro hz
    have hγz : ContDiff ℝ ∞ (fun t => γ (z, t)) :=
      hγ.comp (contDiff_const.prodMk contDiff_id)
    have hder := ((A z).contDiff.differentiable (by simp) (γ (z, s))).hasFDerivAt.comp_hasDerivAt
      s ((hγz.differentiable (by simp) s).hasDerivAt)
    have heq : (A z : E2 → E2) ∘ (fun t => γ (z, t)) =
        (fun t => c (θ z) (sphereCircleParameter e t)) := by
      funext t
      exact (A z).apply_symm_apply _
    rw [heq, hz, map_zero] at hder
    exact deriv_curveFamily_circleParameter_ne_zero e c hc (θ z) s
      ((hmargin (θ z) (hband (θ z) (hθrange z))).2 _) hder.deriv
  have hγi (z s t : ℝ) (hh : γ (z, s) = γ (z, t)) :
      sphereCircleParameter e s = sphereCircleParameter e t :=
    (hmargin (θ z) (hband (θ z) (hθrange z))).1 ((A z).symm.toEquiv.injective hh)
  obtain ⟨H, hH, hHi, hHb⟩ :=
    exists_unit_curve_ambient_extension e q0 γ hγ hγnorm hγper hγne hγi
  refine ⟨fun z => (H z).trans (A z), hA.comp (contDiff_fst.prodMk hH),
    hHi.comp (contDiff_fst.prodMk hAi), ?_⟩
  intro z hz q
  obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
  change A z (H z (sphereCircleParameter e s : E2)) = _
  rw [hHb]
  change A z ((A z).symm (c (θ z) (sphereCircleParameter e s))) = _
  rw [Diffeomorph.apply_symm_apply, hθid z hz]

theorem planarSchoenfliesService : PlanarSchoenfliesService := by
  refine ⟨nonempty_planarSchoenfliesData, ?_⟩
  intro a b c hab hc hemb
  obtain ⟨Φ, hΦ, _, hboundary⟩ :=
    exists_planar_curve_family_ambient_diffeomorphs a b c hab hc hemb
  exact nonempty_planarSchoenfliesFamilyData_of_diffeomorphs a b c Φ hΦ hboundary

end PoincareConjecture.M25.Topology3D
