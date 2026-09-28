import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.StaticAngularJets
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.UniformSampledPolygonCloseness
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.TwoEndpointMinimizingInterpolator
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.PeriodicC1LoopFamily
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicPolygon
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonGeometry
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceAngularJets
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.ProjIcc













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology Bundle intervalIntegral ENNReal

universe u

namespace PoincareConjecture

open M63 Proofs.M58




theorem m64_exists_uniform_sampled_smooth_loop_family
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (Set.univ : Set M))
    (Gamma : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∃ polygon : LoopTwoSphere →
        M63GeodesicPolygon g D N,
        (∀ z (j : Fin N), (polygon z).vertices j =
          periodicFreeLoop (Gamma z) (m63CellLeft N j)) ∧
        ∃ family : C(LoopTwoSphere, C1FreeLoopSpace (M := M)),
          (∀ z x, periodicFreeLoop (family z) x =
            m63FlattenedPolygon (polygon z) x) ∧
          (∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
            (periodicFreeLoop (family z))) ∧
          Continuous (fun p : LoopTwoSphere × ℝ =>
            m63AngularFirstJet (n := 3) (periodicFreeLoop (family p.1)) p.2) ∧
          Continuous (fun p : LoopTwoSphere × ℝ =>
            m63AngularSecondJet D
              (periodicFreeLoop (family p.1)) p.2) ∧
          ∀ z (x : LoopCircle),
            g.edist (family z x) (Gamma z x) < ENNReal.ofReal epsilon := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let sphereEquiv : Metric.sphere (0 : LoopAmbient) 1 ≃ₜ LoopTwoSphere :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  let : CompactSpace LoopTwoSphere := sphereEquiv.compactSpace
  let gamma : LoopTwoSphere → ℝ → M := fun z => periodicFreeLoop (Gamma z)
  let speed : LoopTwoSphere → ℝ → ℝ := fun z t =>
    g.tangentNorm (gamma z t) (curveVelocity (gamma z) t)
  have hP : 0 < curvePeriod := Real.two_pi_pos
  have hgamma (z : LoopTwoSphere) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (gamma z) :=
    contMDiff_periodicFreeLoop (Gamma z)
  have hperiod (z : LoopTwoSphere) : Function.Periodic (gamma z) curvePeriod :=
    periodic_periodicFreeLoop (Gamma z)
  have hspeed (z : LoopTwoSphere) : Continuous (speed z) :=
    continuous_freeLoopSpeed g (Gamma z)
  have hjet : Continuous (fun w : LoopTwoSphere × ℝ =>
      m63AngularFirstJet (gamma w.1) w.2) :=
    m63AngularFirstJet_continuous.comp
      ((Gamma.continuous.comp continuous_fst).prodMk continuous_snd)
  have hvalue : Continuous (fun w : LoopTwoSphere × ℝ => gamma w.1 w.2) :=
    (FiberBundle.continuous_proj LoopAmbient (TangentSpace (𝓡 3))).comp hjet
  have hcompactJet : Continuous
      (fun w : LoopTwoSphere × Icc (0 : ℝ) curvePeriod =>
        m63AngularFirstJet (gamma w.1) w.2) :=
    hjet.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hspeedJoint : Continuous (fun w : LoopTwoSphere × Icc (0 : ℝ) curvePeriod =>
      speed w.1 w.2) :=
    (hcompactJet.inner_bundle hcompactJet).sqrt
  obtain ⟨S0, hS0⟩ := (isCompact_range hspeedJoint).bddAbove
  let S : ℝ := max S0 0
  have hS : 0 ≤ S := le_max_right _ _
  have hspeedBound (z : LoopTwoSphere) {t : ℝ} (ht : t ∈ Icc 0 curvePeriod) :
      speed z t ≤ S := by
    have hm : speed z t ∈ range
        (fun w : LoopTwoSphere × Icc (0 : ℝ) curvePeriod => speed w.1 w.2) :=
      ⟨(z, ⟨t, ht⟩), rfl⟩
    exact (hS0 hm).trans (le_max_left _ _)
  have hsubarc (z : LoopTwoSphere) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
      (ht : t ≤ curvePeriod) : g.edist (gamma z s) (gamma z t) ≤
        ENNReal.ofReal (S * (t - s)) := by
    have hd := g.edist_le_pathELength_of_mem_Icc (hgamma z).contMDiffOn
      (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
    rw [M04.pathELength_eq_ofReal_integral_pathSpeed g (hgamma z) hst] at hd
    apply hd.trans (ENNReal.ofReal_le_ofReal ?_)
    have hi := intervalIntegral.integral_mono_on (μ := volume) hst
      ((hspeed z).intervalIntegrable s t) (continuous_const.intervalIntegrable s t)
      (fun v hv => hspeedBound z ⟨hs.trans hv.1, hv.2.trans ht⟩)
    simpa +instances only [intervalIntegral.integral_const, smul_eq_mul, mul_comm,
      speed, M04.pathSpeed, curveVelocity] using! hi
  obtain ⟨r, hr, H, hH, hgeom, _hdiag, _huniq⟩ :=
    exists_smooth_minimizing_interpolator g hcompact
  let eta : ℝ := min r (epsilon / 3)
  have heta : 0 < eta := lt_min hr (by positivity)
  obtain ⟨N0, hN0, hfine⟩ := m64_exists_mesh_threshold (S := (S + 1) / 2) heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN0N
  have hN : 0 < N := hN0.trans_le hN0N
  let ell := m63CellLength N
  have hell : 0 < ell := m63CellLength_pos hN
  have hNell : (N : ℝ) * ell = curvePeriod := m63_count_mul_cellLength hN
  have hmesh : (S + 1) * ell < eta := by
    nlinarith only [hfine N hN0N]
  have hSell : S * ell < eta :=
    (mul_lt_mul_of_pos_right (lt_add_one S) hell).trans hmesh
  have hcellBounds (j : Fin N) : 0 ≤ m63CellLeft N j ∧
      m63CellLeft N j + ell ≤ curvePeriod := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hell.le, ?_⟩
    have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    calc
      _ = ((j.val : ℝ) + 1) * ell := by dsimp only [m63CellLeft, ell]; ring
      _ ≤ (N : ℝ) * ell := mul_le_mul_of_nonneg_right hj hell.le
      _ = curvePeriod := hNell
  let vertices : LoopTwoSphere → Fin N → M := fun z j => gamma z (m63CellLeft N j)
  have hvcont (j : Fin N) : Continuous (fun z => vertices z j) :=
    hvalue.comp (continuous_id.prodMk continuous_const)
  have hadjBound (z : LoopTwoSphere) (j : Fin N) :
      g.edist (vertices z j) (vertices z (finRotate N j)) ≤ ENNReal.ofReal (S * ell) := by
    have hh := hsubarc z (hcellBounds j).1 (le_add_of_nonneg_right hell.le)
      (hcellBounds j).2
    rw [← m63PeriodicLoop_cell_finish (hperiod z) hN j] at hh
    simpa only [add_sub_cancel_left] using hh
  have hadj (z : LoopTwoSphere) (j : Fin N) :
      g.edist (vertices z j) (vertices z (finRotate N j)) < ENNReal.ofReal r :=
    (hadjBound z j).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr
      (hSell.trans_le (min_le_left _ _)))
  have hunit : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hscale {s : ℝ} (hs : s ∈ Icc 0 ell) : ell⁻¹ * s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (inv_nonneg.mpr hell.le) hs.1, ?_⟩
    calc
      ell⁻¹ * s ≤ ell⁻¹ * ell := mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = 1 := inv_mul_cancel₀ hell.ne'
  let side (z : LoopTwoSphere) (j : Fin N) :
      M63MinimizingGeodesicSide g D ell
        (vertices z j) (vertices z (finRotate N j)) := by
    let p := vertices z j
    let q := vertices z (finRotate N j)
    let alpha : ℝ → M := fun s => H (ell⁻¹ * s, p, q)
    let V : Set ℝ := (fun s : ℝ => ell⁻¹ * s) ⁻¹' Ioo (-1 : ℝ) 2
    have hgeo := (hgeom p q (hadj z j)).2.2.1
    have halpha : g.IsGeodesicOn alpha V := hgeo.comp_mul ell⁻¹
    have hsub : Icc 0 ell ⊆ V := fun _ hs => hunit (hscale hs)
    have hconstant (s : ℝ) (hs : s ∈ Icc 0 ell) :
        g.tangentNorm (alpha s) (curveVelocity alpha s) = (g.edist p q).toReal / ell := by
      have hdiff := (hgeo.contMDiffAt_infty (hsub hs)).mdifferentiableAt (by simp)
      have hparam : HasDerivAt (fun v : ℝ => ell⁻¹ * v) ell⁻¹ s := by
        simpa using (hasDerivAt_id s).const_mul ell⁻¹
      have hCs : g.tangentNorm (H (ell⁻¹ * s, p, q))
          (curveVelocity (n := 3) (fun v => H (v, p, q)) (ell⁻¹ * s)) =
            (g.edist p q).toReal := by
        simpa only [curveVelocity] using! (hgeom p q (hadj z j)).2.2.2.1 _ (hsub hs)
      change g.tangentNorm (H (ell⁻¹ * s, p, q))
        (curveVelocity (fun v => H (ell⁻¹ * v, p, q)) s) = _
      rw [curveVelocity_comp hdiff hparam, g.tangentNorm_smul,
        abs_of_nonneg (inv_nonneg.mpr hell.le), hCs]
      exact (div_eq_inv_mul _ _).symm
    exact {
      map := alpha
      domain := V
      domain_open := isOpen_Ioo.preimage (continuous_const.mul continuous_id)
      interval_subset := hsub
      smooth := halpha.contMDiffOn_infty
      start := by simpa only [alpha, mul_zero] using (hgeom p q (hadj z j)).1
      finish := by simpa only [alpha, inv_mul_cancel₀ hell.ne'] using
        (hgeom p q (hadj z j)).2.1
      speed := (g.edist p q).toReal / ell
      speed_nonnegative := div_nonneg ENNReal.toReal_nonneg hell.le
      constant_speed := hconstant
      equation := fun _ hs => halpha.pullback_velocity_eq_zero D hs
      minimizing := by
        rw [g.pathELength_eq_of_tangentNorm_eq hconstant, sub_zero,
          ← ENNReal.ofReal_mul (div_nonneg ENNReal.toReal_nonneg hell.le),
          div_mul_cancel₀ _ hell.ne', ENNReal.ofReal_toReal]
        exact ne_top_of_lt (hadj z j) }
  let polygon : LoopTwoSphere → M63GeodesicPolygon g D N :=
    fun z => geodesicPolygonOfSides hN ⟨vertices z⟩ (side z)
  let beta : LoopTwoSphere → ℝ → M := fun z => m63FlattenedPolygon (polygon z)
  have hbeta (z : LoopTwoSphere) : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (beta z) :=
    m63FlattenedPolygon_smooth (polygon z) hN
  have hbetaP (z : LoopTwoSphere) : Function.Periodic (beta z) curvePeriod :=
    m63FlattenedPolygon_periodic (polygon z) hN
  let rN : ℝ → ℝ := fun s => ell⁻¹ * m63Flattening N s
  have hrN : ContDiff ℝ ∞ rN := contDiff_const.mul (m63Flattening_smooth N)
  have hrN1 : ContDiff ℝ ∞ (deriv rN) := by simpa using hrN.iterate_deriv 1
  have hrN2 : ContDiff ℝ ∞ (deriv (deriv rN)) := by simpa using hrN.iterate_deriv 2
  have hrNmem {s : ℝ} (hs : s ∈ Icc 0 ell) : rN s ∈ Icc (0 : ℝ) 1 := by
    apply hscale
    simpa only [Int.cast_zero, zero_mul, zero_add, sub_zero] using
      m63Flattening_mem_cell hN 0 hs
  have hrN0 : rN 0 = 0 := by simp [rN, m63Flattening_zero]
  have hrNell : rN ell = 1 := by
    have hh : m63Flattening N ell = ell := by
      simpa only [Int.cast_one, one_mul] using m63Flattening_vertex hN 1
    change ell⁻¹ * m63Flattening N ell = 1
    rw [hh, inv_mul_cancel₀ hell.ne']
  have hrNder (s : ℝ) : deriv rN s = ell⁻¹ * m63Profile N s :=
    ((m63Flattening_hasDerivAt N s).const_mul ell⁻¹).deriv
  have hrNder2 (s : ℝ) : deriv (deriv rN) s = ell⁻¹ * deriv (m63Profile N) s := by
    rw [show deriv rN = (fun v => ell⁻¹ * m63Profile N v) from funext hrNder]
    exact (((m63Profile_smooth N).differentiable (by simp) s).hasDerivAt.const_mul _).deriv
  have hflat (j : ℤ) : deriv rN ((j : ℝ) * ell) = 0 ∧
      deriv (deriv rN) ((j : ℝ) * ell) = 0 := by
    rw [hrNder, hrNder2]
    constructor
    · simpa only [iteratedDeriv_zero, mul_zero] using
        congrArg (fun x : ℝ => ell⁻¹ * x) (m63Profile_flat hN 0 j)
    · simpa only [iteratedDeriv_one, mul_zero] using
        congrArg (fun x : ℝ => ell⁻¹ * x) (m63Profile_flat hN 1 j)
  have hflat0 : deriv rN 0 = 0 ∧ deriv (deriv rN) 0 = 0 := by simpa using hflat 0
  have hflatell : deriv rN ell = 0 ∧ deriv (deriv rN) ell = 0 := by simpa using hflat 1
  have hbetaCell (z : LoopTwoSphere) (j : Fin N) {s : ℝ} (hs : s ∈ Icc 0 ell) :
      beta z (m63CellLeft N j + s) =
        H (rN s, vertices z j, vertices z (finRotate N j)) := by
    have hh := m63FlattenedPolygon_cell_agreement (polygon z) hN j hs
    have hf : m63Flattening N (m63CellLeft N j + s) - m63CellLeft N j =
        m63Flattening N s := by
      have hshift : m63Flattening N (s + m63CellLeft N j) =
          m63Flattening N s + m63CellLeft N j := by
        simpa only [Int.cast_natCast, m63CellLeft] using
          m63Flattening_int_cell_shift hN s (j.val : ℤ)
      rw [add_comm (m63CellLeft N j) s, hshift, add_sub_cancel_right]
    rw [hf] at hh
    exact hh
  let z0 : LoopTwoSphere := ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
  let : Nonempty M := ⟨gamma z0 0⟩
  obtain ⟨d, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hrhoe, _hnearest, _hunique⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  let W := EuclideanSpace ℝ (Fin d)
  let I := (𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))
  let Omega : Set (ℝ × (M × M)) := Ioo (-1 : ℝ) 2 ×ˢ
    {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}
  have hOmega : IsOpen Omega := isOpen_Ioo.prod
    (isOpen_lt (continuous_fst.edist continuous_snd) continuous_const)
  let T0 : ℝ × (M × M) → W := fun w => e (H w)
  let T1 : ℝ × (M × M) → W := fun w => deriv (fun s => T0 (s, w.2)) w.1
  let T2 : ℝ × (M × M) → W := fun w => deriv (fun s => T1 (s, w.2)) w.1

  have hpartial (f : ℝ × (M × M) → W)
      (hf : ContMDiffOn I 𝓘(ℝ, W) ∞ f Omega) :
      ContMDiffOn I 𝓘(ℝ, W) ∞ (fun w => deriv (fun s => f (s, w.2)) w.1) Omega := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
        (fun s : ℝ => (⟨s, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    have hzero : ContMDiff ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)).tangent ∞
        (fun pq : M × M => (⟨pq, 0⟩ : TangentBundle ((𝓡 3).prod (𝓡 3)) (M × M))) :=
      contMDiff_zeroSection ℝ (TangentSpace ((𝓡 3).prod (𝓡 3)))
    have hsection : ContMDiff I I.tangent ∞
        (fun w : ℝ × (M × M) => (⟨w, (1, 0)⟩ : TangentBundle I (ℝ × (M × M)))) :=
      contMDiff_equivTangentBundleProd_symm.comp
        ((hone.comp contMDiff_fst).prodMk (hzero.comp contMDiff_snd))
    have ht := hf.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hOmega.uniqueMDiffOn
    have hc := (contMDiff_snd_tangentBundle_modelSpace W 𝓘(ℝ, W)).comp_contMDiffOn
      (ht.comp hsection.contMDiffOn (fun w (hw : w ∈ Omega) => hw))
    apply hc.congr
    intro w hw
    have hdf := (hf.contMDiffAt (hOmega.mem_nhds hw)).mdifferentiableAt (by simp)
    have hi : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (s, w.2)) w.1 :=
      mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hchain := mfderiv_comp_apply w.1 hdf hi (1 : ℝ)
    have hinclusion : mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (s, w.2)) w.1 1 = (1, 0) := by
      have hprod := mfderiv_prodMk (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
        (I'' := (𝓡 3).prod (𝓡 3)) (f := id)
        (g := fun _ : ℝ => w.2) (x := w.1) mdifferentiableAt_id mdifferentiableAt_const
      rw [mfderiv_id, mfderiv_const] at hprod
      exact congrArg (fun L : ℝ →L[ℝ] (ℝ × (LoopAmbient × LoopAmbient)) => L 1) hprod
    rw [hinclusion] at hchain
    change deriv (fun s => f (s, w.2)) w.1 = mfderivWithin I 𝓘(ℝ, W) f Omega w (1, 0)
    rw [mfderivWithin_of_isOpen hOmega hw]
    simpa +instances only [Function.comp_def, mfderiv_eq_fderiv] using! hchain
  have hT0 : ContMDiffOn I 𝓘(ℝ, W) ∞ T0 Omega := he.comp_contMDiffOn hH
  have hT1 : ContMDiffOn I 𝓘(ℝ, W) ∞ T1 Omega := hpartial T0 hT0
  have hT2 : ContMDiffOn I 𝓘(ℝ, W) ∞ T2 Omega := hpartial T1 hT1
  have hslice (f : ℝ × (M × M) → W) (hf : ContMDiffOn I 𝓘(ℝ, W) ∞ f Omega)
      (z : LoopTwoSphere) (j : Fin N) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 2) :
      DifferentiableAt ℝ (fun s => f (s, vertices z j, vertices z (finRotate N j))) t := by
    have hm : (t, vertices z j, vertices z (finRotate N j)) ∈ Omega := ⟨ht, hadj z j⟩
    exact mdifferentiableAt_iff_differentiableAt.mp
      (((hf.contMDiffAt (hOmega.mem_nhds hm)).mdifferentiableAt (by simp)).comp t
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const))
  let B : LoopTwoSphere → ℝ → W := fun z x => e (beta z x)
  have hB (z : LoopTwoSphere) : ContDiff ℝ ∞ (B z) := (he.comp (hbeta z)).contDiff
  have hB1 (z : LoopTwoSphere) : ContDiff ℝ ∞ (deriv (B z)) := by
    simpa using (hB z).iterate_deriv 1
  let J : LoopTwoSphere → ℝ → (W × W) × W := fun z x =>
    ((B z x, deriv (B z) x), deriv (deriv (B z)) x)
  let cell : Fin N → LoopTwoSphere → ℝ → (W × W) × W := fun j z s =>
    ((T0 (rN s, vertices z j, vertices z (finRotate N j)),
      deriv rN s • T1 (rN s, vertices z j, vertices z (finRotate N j))),
      (deriv rN s) ^ 2 • T2 (rN s, vertices z j, vertices z (finRotate N j)) +
        deriv (deriv rN) s • T1 (rN s, vertices z j, vertices z (finRotate N j)))

  have hcellJ (z : LoopTwoSphere) (j : Fin N) {s : ℝ} (hs : s ∈ Icc 0 ell) :
      J z (m63CellLeft N j + s) = cell j z s := by
    let q : ℝ → W := fun v => T0 (rN v, vertices z j, vertices z (finRotate N j))
    let q1 : ℝ → W := fun v => deriv rN v •
      T1 (rN v, vertices z j, vertices z (finRotate N j))
    have hqd (v : ℝ) (hv : v ∈ Icc 0 ell) : HasDerivAt q (q1 v) v := by
      exact ((hslice T0 hT0 z j (hunit (hrNmem hv))).hasDerivAt.scomp v
        ((hrN.differentiable (by simp) v).hasDerivAt))
    have hq1d (v : ℝ) (hv : v ∈ Icc 0 ell) : HasDerivAt q1
        ((deriv rN v) ^ 2 • T2 (rN v, vertices z j, vertices z (finRotate N j)) +
          deriv (deriv rN) v • T1 (rN v, vertices z j, vertices z (finRotate N j))) v := by
      have hd := ((hrN1.differentiable (by simp) v).hasDerivAt).smul
        ((hslice T1 hT1 z j (hunit (hrNmem hv))).hasDerivAt.scomp v
          ((hrN.differentiable (by simp) v).hasDerivAt))
      simpa +instances only [q1, T2, Pi.smul_apply, Function.comp_def, smul_smul, pow_two]
        using! hd
    have heq : EqOn (fun v => B z (m63CellLeft N j + v)) q (Icc 0 ell) :=
      fun v hv => congrArg e (hbetaCell z j hv)
    have hfirst (v : ℝ) (hv : v ∈ Icc 0 ell) :
        deriv (B z) (m63CellLeft N j + v) = q1 v := by
      have hu := uniqueDiffOn_Icc hell v hv
      have hdf : DifferentiableAt ℝ (fun w => B z (m63CellLeft N j + w)) v :=
        ((hB z).differentiable (by simp) _).comp v
          ((differentiableAt_const (m63CellLeft N j)).add differentiableAt_id)
      have hd := derivWithin_congr heq (heq hv)
      rw [hdf.derivWithin hu, (hqd v hv).differentiableAt.derivWithin hu,
        deriv_comp_const_add, (hqd v hv).deriv] at hd
      exact hd
    have hsecond : deriv (deriv (B z)) (m63CellLeft N j + s) =
        (cell j z s).2 := by
      have hu := uniqueDiffOn_Icc hell s hs
      have hdf : DifferentiableAt ℝ (fun w => deriv (B z) (m63CellLeft N j + w)) s :=
        ((hB1 z).differentiable (by simp) _).comp s
          ((differentiableAt_const (m63CellLeft N j)).add differentiableAt_id)
      have hd := derivWithin_congr hfirst (hfirst s hs)
      rw [hdf.derivWithin hu, (hq1d s hs).differentiableAt.derivWithin hu,
        deriv_comp_const_add, (hq1d s hs).deriv] at hd
      exact hd
    exact Prod.ext (Prod.ext (heq hs) (hfirst s hs)) hsecond
  let clamp : ℝ → ℝ := fun s => projIcc 0 1 (by norm_num) (rN s)
  have hclamp : Continuous clamp := continuous_subtype_val.comp
    (continuous_projIcc.comp hrN.continuous)
  have hclampMem (s : ℝ) : clamp s ∈ Icc (0 : ℝ) 1 := (projIcc _ _ _ _).property
  have hclampEq {s : ℝ} (hs : s ∈ Icc 0 ell) : clamp s = rN s := by
    exact congrArg Subtype.val (projIcc_of_mem (by norm_num) (hrNmem hs))
  let data : Fin N → LoopTwoSphere × ℝ → (W × W) × W := fun j w =>
    ((T0 (clamp w.2, vertices w.1 j, vertices w.1 (finRotate N j)),
      deriv rN w.2 • T1 (clamp w.2, vertices w.1 j, vertices w.1 (finRotate N j))),
      (deriv rN w.2) ^ 2 • T2 (clamp w.2, vertices w.1 j, vertices w.1 (finRotate N j)) +
        deriv (deriv rN) w.2 • T1 (clamp w.2, vertices w.1 j, vertices w.1 (finRotate N j)))
  have hdata (j : Fin N) : Continuous (data j) := by
    let input : LoopTwoSphere × ℝ → ℝ × (M × M) := fun w =>
      (clamp w.2, vertices w.1 j, vertices w.1 (finRotate N j))
    have hi : Continuous input := (hclamp.comp continuous_snd).prodMk
      (((hvcont j).comp continuous_fst).prodMk ((hvcont (finRotate N j)).comp continuous_fst))
    have hm (w : LoopTwoSphere × ℝ) : input w ∈ Omega :=
      ⟨hunit (hclampMem w.2), hadj w.1 j⟩
    have h0 := hT0.continuousOn.comp_continuous (f := input) hi hm
    have h1 := hT1.continuousOn.comp_continuous (f := input) hi hm
    have h2 := hT2.continuousOn.comp_continuous (f := input) hi hm
    exact (h0.prodMk ((hrN1.continuous.comp continuous_snd).smul h1)).prodMk
      ((((hrN1.continuous.comp continuous_snd).pow 2).smul h2).add
        ((hrN2.continuous.comp continuous_snd).smul h1))
  let alpha : Fin N → ℝ → C(LoopTwoSphere, (W × W) × W) := fun j s =>
    ⟨fun z => data j (z, s), (hdata j).comp (continuous_id.prodMk continuous_const)⟩
  have halpha (j : Fin N) : Continuous (alpha j) :=
    ContinuousMap.continuous_of_continuous_uncurry _ ((hdata j).comp continuous_swap)
  have halphaCell (j : Fin N) (z : LoopTwoSphere) {s : ℝ} (hs : s ∈ Icc 0 ell) :
      alpha j s z = cell j z s := by
    change data j (z, s) = cell j z s
    dsimp only [data]
    rw [hclampEq hs]
  have hmatch (j : Fin N) : alpha j ell = alpha (finRotate N j) 0 := by
    apply ContinuousMap.ext
    intro z
    rw [halphaCell j z ⟨hell.le, le_rfl⟩,
      halphaCell (finRotate N j) z ⟨le_rfl, hell.le⟩]
    simp only [cell, hrN0, hrNell, hflat0.1, hflat0.2, hflatell.1, hflatell.2,
      zero_smul, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add]
    rw [show T0 (1, vertices z j, vertices z (finRotate N j)) =
      e (vertices z (finRotate N j)) from congrArg e (hgeom _ _ (hadj z j)).2.1,
      show T0 (0, vertices z (finRotate N j), vertices z (finRotate N (finRotate N j))) =
        e (vertices z (finRotate N j)) from congrArg e (hgeom _ _ (hadj z (finRotate N j))).1]
  obtain ⟨Q, hQ, hQP, hQcell⟩ := exists_continuous_periodic_concat hN hell alpha
    (fun j => (halpha j).continuousOn) hmatch
  rw [hNell] at hQP
  have hcover {x : ℝ} (hx : x ∈ Icc 0 curvePeriod) :
      ∃ j : Fin N, ∃ s ∈ Icc 0 ell, x = m63CellLeft N j + s := by
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · have hxdiv : 0 ≤ x / ell := div_nonneg hx.1 hell.le
      have hj : Nat.floor (x / ell) < N := (Nat.floor_lt hxdiv).mpr
        ((div_lt_iff₀ hell).mpr (by simpa only [hNell] using hlt))
      let j : Fin N := ⟨Nat.floor (x / ell), hj⟩
      refine ⟨j, x - m63CellLeft N j, ⟨?_, ?_⟩, by ring⟩
      · exact sub_nonneg.mpr ((le_div_iff₀ hell).mp (Nat.floor_le hxdiv))
      · have hh := (div_lt_iff₀ hell).mp (Nat.lt_floor_add_one (x / ell))
        change x - (Nat.floor (x / ell) : ℝ) * ell ≤ ell
        nlinarith only [hh]
    · let j : Fin N := ⟨N - 1, by omega⟩
      refine ⟨j, ell, ⟨hell.le, le_rfl⟩, ?_⟩
      have hn : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (by omega : N - 1 + 1 = N)
      change curvePeriod = ((N - 1 : ℕ) : ℝ) * ell + ell
      rw [← hNell, ← hn]
      ring
  have hJperiod (z : LoopTwoSphere) : Function.Periodic (J z) curvePeriod := by
    have hp0 : Function.Periodic (B z) curvePeriod := fun x => congrArg e (hbetaP z x)
    have hp1 := hp0.deriv_of_differentiable ((hB z).differentiable (by simp))
    have hp2 := hp1.deriv_of_differentiable ((hB1 z).differentiable (by simp))
    exact fun x => Prod.ext (Prod.ext (hp0 x) (hp1 x)) (hp2 x)
  have hQeq (z : LoopTwoSphere) (x : ℝ) : Q x z = J z x := by
    have hon {x : ℝ} (hx : x ∈ Icc 0 curvePeriod) : Q x z = J z x := by
      obtain ⟨j, s, hs, rfl⟩ := hcover hx
      rw [show m63CellLeft N j = (j.val : ℝ) * ell from rfl, hQcell j s hs]
      exact (halphaCell j z hs).trans (hcellJ z j hs).symm
    let k : ℤ := Int.floor (x / curvePeriod)
    let y : ℝ := x - (k : ℝ) * curvePeriod
    have hy : y ∈ Icc 0 curvePeriod := by
      have h0 := (le_div_iff₀ hP).mp (Int.floor_le (x / curvePeriod))
      have h1 := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (x / curvePeriod))
      dsimp only [y, k]
      constructor <;> linarith only [h0, h1]
    have hx : x = y + (k : ℝ) * curvePeriod := by dsimp [y]; ring
    rw [hx, hQP.int_mul k y, (hJperiod z).int_mul k y]
    exact hon hy
  have hJ : Continuous (fun w : LoopTwoSphere × ℝ => J w.1 w.2) := by
    have hc := continuous_eval.comp ((hQ.comp continuous_snd).prodMk continuous_fst)
    exact hc.congr (fun w => hQeq w.1 w.2)
  obtain ⟨hbetaC, hbetaJ1, hbetaJ2⟩ :=
    m64_continuous_angular_jets_of_embedded_jets D beta
      (fun z => (hbeta z).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      he hU heU hrho hrhoe hJ.fst.fst hJ.fst.snd hJ.snd
  obtain ⟨family, hfamily⟩ := exists_continuous_c1Loop_family_of_periodic beta hbetaP
    (fun z => (hbeta z).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hbetaC hbetaJ1
  have hfamilyEq (z : LoopTwoSphere) : periodicFreeLoop (family z) = beta z := funext (hfamily z)
  refine ⟨polygon, fun _ _ => rfl, family, hfamily,
    fun z => by rw [hfamilyEq z]; exact hbeta z, ?_, ?_, ?_⟩
  · simpa only [hfamilyEq] using hbetaJ1
  · simpa only [hfamilyEq] using hbetaJ2
  · intro z x
    obtain ⟨t, ht, htx⟩ := exists_angularPoint x
    have ht' : t ∈ Icc 0 curvePeriod := ht
    obtain ⟨j, s, hs, hts⟩ := hcover ht'
    have hpoint : g.edist (beta z t) (vertices z j) ≤ ENNReal.ofReal (S * ell) := by
      rw [hts, hbetaCell z j hs]
      have hh := (hgeom _ _ (hadj z j)).2.2.2.2.2
        (rN s) (hrNmem hs) 0 ⟨le_rfl, zero_le_one⟩
      rw [(hgeom _ _ (hadj z j)).1, sub_zero,
        abs_of_nonneg (hrNmem hs).1] at hh
      rw [hh]
      calc
        _ ≤ 1 * g.edist (vertices z j) (vertices z (finRotate N j)) :=
          mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal (hrNmem hs).2) _
        _ ≤ _ := by simpa only [one_mul] using hadjBound z j
    have horiginal : g.edist (vertices z j) (gamma z t) ≤ ENNReal.ofReal (S * ell) := by
      have horder : m63CellLeft N j ≤ t := by linarith only [hs.1, hts]
      have hh := hsubarc z (hcellBounds j).1 horder ht'.2
      apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul_of_nonneg_left _ hS
      linarith only [hs.2, hts]
    have hnear : g.edist (beta z t) (gamma z t) < ENNReal.ofReal epsilon := by
      apply (edist_triangle _ (vertices z j) _).trans_lt
      apply (add_le_add hpoint horiginal).trans_lt
      rw [← ENNReal.ofReal_add (mul_nonneg hS hell.le) (mul_nonneg hS hell.le)]
      apply (ENNReal.ofReal_lt_ofReal_iff hepsilon).mpr
      have hh := hSell.trans_le (min_le_right r (epsilon / 3))
      linarith only [hh, hepsilon]
    have hcircle : (⟨angularPoint t, norm_angularPoint t⟩ : LoopCircle) = x :=
      Subtype.ext htx
    have hboundary (loop : C1FreeLoopSpace (M := M)) :
        periodicFreeLoop loop t = loop x := by
      calc
        _ = loop ⟨angularPoint t, norm_angularPoint t⟩ :=
          loop.boundary ⟨angularPoint t, norm_angularPoint t⟩
        _ = loop x := congrArg loop hcircle
    have htrace : family z x = beta z t :=
      (hboundary (family z)).symm.trans (hfamily z t)
    have horiginal : gamma z t = Gamma z x := hboundary (Gamma z)
    change g.edist (family z x) (Gamma z x) < _
    rw [htrace, ← horiginal]
    exact hnear

end PoincareConjecture
