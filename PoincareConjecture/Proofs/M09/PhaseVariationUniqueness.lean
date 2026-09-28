import PoincareConjecture.Proofs.M09.ExponentialPhaseLinearization
import PoincareConjecture.Proofs.M09.TangentPhaseZero
import PoincareConjecture.Proofs.M09.WithinODEUniqueness








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialLinePhase_variation_zero_implies
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (c : ℝ) (hc : c ∈ sqrtParameterInterval 0 b) (x0 : M)
    (hx0 : A.squareFamily Z c ∈ (chartAt Q x0).source)
    (hzero : deriv (fun u ↦ initialLineChartPhase A Z W x0 (c, u)) 0 = 0) : W = 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let K := sqrtParameterInterval 0 b
  let H : ℝ × ℝ → M := fun z ↦ V.squareFamily z.1 z.2
  let P : M → ℝ × ℝ → Q × Q := initialLineChartPhase A Z W
  let D : M → ℝ → Q × Q := fun x s ↦ deriv (fun u ↦ P x (s, u)) 0
  let Ω : M → Set (ℝ × ℝ) := fun x ↦ V.squareDomain ∩ H ⁻¹' (chartAt Q x).source
  let U : M → Set ℝ := fun x ↦ ((fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' Ω x) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hΩ (x : M) : IsOpen (Ω x) := hH.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt Q x).open_source
  have hU (x : M) : IsOpen (U x) :=
    ((hΩ x).preimage (continuous_id.prodMk continuous_const)).inter isOpen_Ioo
  have hP (x : M) : ContDiffOn ℝ ∞ (P x) (Ω x) :=
    initialLineChartPhase_contDiffOn A Z W b hb hmax x
  have hD (x : M) : ContDiffOn ℝ ∞ (D x) (U x) :=
    (contDiffOn_partial_snd (P x) (Ω x) (hΩ x) (hP x)).mono Set.inter_subset_left
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp only [K, sqrtParameterInterval, Real.sqrt_zero]
  have hKU (s : ℝ) (hs : s ∈ K) (x : M) (hx : A.squareFamily Z s ∈ (chartAt Q x).source) :
      s ∈ U x := by
    refine ⟨⟨V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩, ?_⟩, ?_⟩
    · change A.squareFamily (Z + (0 : ℝ) • W) s ∈ (chartAt Q x).source
      simpa only [zero_smul, add_zero] using hx
    · rw [hK] at hs
      exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
        hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hsource (x : M) (s : ℝ) (hs : s ∈ U x) :
      A.squareFamily Z s ∈ (chartAt Q x).source := by
    have h := hs.1.2
    change A.squareFamily (Z + (0 : ℝ) • W) s ∈ (chartAt Q x).source at h
    simpa only [zero_smul, add_zero] using h
  have hparam (x : M) (s : ℝ) (hs : s ∈ U x) :
      HasDerivAt (fun u ↦ P x (s, u)) (D x s) 0 :=
    (hasDerivAt_slice_snd (P x) s 0
      (((hP x).contDiffAt ((hΩ x).mem_nhds hs.1)).differentiableAt (by simp))).differentiableAt.hasDerivAt
  have hphase (s : ℝ) (hs : s ∈ K) :
      ContinuousAt (fun u ↦ initialLinePhase A Z W (s, u)) 0 := by
    have hmem : (s, (0 : ℝ)) ∈ V.squareDomain :=
      V.square_contains ⟨hs, neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
    exact (((initialLinePhase_contMDiffOn A Z W b hb hmax).contMDiffAt
      (V.square_open.mem_nhds hmem)).comp 0
        (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt).continuousAt
  have htransfer (s : ℝ) (hs : s ∈ K) (x y : M)
      (hx : A.squareFamily Z s ∈ (chartAt Q x).source)
      (hy : A.squareFamily Z s ∈ (chartAt Q y).source) (hz : D x s = 0) : D y s = 0 := by
    have hx' : (initialLinePhase A Z W (s, 0)).proj ∈ (chartAt Q x).source := by
      simpa only [initialLinePhase, curvePhase, zero_smul, add_zero] using hx
    have hy' : (initialLinePhase A Z W (s, 0)).proj ∈ (chartAt Q y).source := by
      simpa only [initialLinePhase, curvePhase, zero_smul, add_zero] using hy
    have hdx := hparam x s (hKU s hs x hx)
    rw [hz] at hdx
    exact (tangentChartPhase_hasDerivAt_zero_transfer x y
      (fun u ↦ initialLinePhase A Z W (s, u)) 0 (hphase s hs) hx' hy' hdx).deriv
  have hlocal (x : M) (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U x) (hz : D x s = 0) :
      D x =ᶠ[𝓝[K] s] (fun _ ↦ (0 : Q × Q)) := by
    let B := regularizedCoordinatePhase (squareChartMetric F T x) (squareChartScalar F T x)
    let S : Set (ℝ × (Q × Q)) :=
      {z | z.1 ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ∧ z.2.1 ∈ (chartAt Q x).target}
    have hS : IsOpen S := (isOpen_Ioo.prod (chartAt Q x).open_target).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hB : ContDiffOn ℝ ∞ B S := regularizedCoordinatePhase_smooth _ _
      (Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) ×ˢ (chartAt Q x).target)
      (isOpen_Ioo.prod (chartAt Q x).open_target)
      (squareChartMetric_smooth F T τmax hτmax hwindow x)
      (squareChartScalar_smooth F hM04 T τmax hτmax hwindow x)
      (fun z hz v hv ↦ squareChartMetric_pos F T x z hz.2 v hv)
    have hPc : ContDiffOn ℝ ∞ (fun t ↦ P x (t, 0)) (U x) :=
      (hP x).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht ↦ ht.1)
    let C : ℝ × (Q × Q) → Q × Q := fun z ↦ fderiv ℝ B (z.1, P x (z.1, 0)) (0, z.2)
    have hpoint : ContDiffOn ℝ ∞ (fun z : ℝ × (Q × Q) ↦ (z.1, P x (z.1, 0)))
        (U x ×ˢ Set.univ) := contDiff_fst.contDiffOn.prodMk
      (hPc.comp contDiff_fst.contDiffOn (fun _ hz ↦ hz.1))
    have hmap : Set.MapsTo (fun z : ℝ × (Q × Q) ↦ (z.1, P x (z.1, 0)))
        (U x ×ˢ Set.univ) S := by
      intro z hz
      exact ⟨hz.1.2, (chartAt Q x).map_source hz.1.1.2⟩
    have hC : ContDiffOn ℝ ∞ C (U x ×ˢ Set.univ) :=
      ((hB.fderiv_of_isOpen hS (m := ∞) (by simp)).comp hpoint hmap).clm_apply
        (contDiff_const.prodMk contDiff_snd).contDiffOn
    have hode : ∀ᶠ t in 𝓝[K] s,
        (t, D x t) ∈ U x ×ˢ Set.univ ∧ HasDerivAt (D x) (C (t, D x t)) t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds ((hU x).mem_nhds hsU)] with t htK htU
      exact ⟨⟨htU, Set.mem_univ _⟩,
        initialLineChartPhase_variation_hasDerivAt hM04 hτmax hwindow A Z W b hb hmax
          x t htK (hsource x t htU)⟩
    have hzeroOde : ∀ᶠ t in 𝓝[K] s,
        (t, (0 : Q × Q)) ∈ U x ×ˢ Set.univ ∧
          HasDerivAt (fun _ : ℝ ↦ (0 : Q × Q)) (C (t, 0)) t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds ((hU x).mem_nhds hsU)] with t ht
      refine ⟨⟨ht, Set.mem_univ _⟩, ?_⟩
      simpa only [C, show ((0 : ℝ), (0 : Q × Q)) = 0 from rfl, map_zero] using
        hasDerivAt_const t (0 : Q × Q)
    exact openODE_eventuallyEqWithin (U x ×ˢ Set.univ) ((hU x).prod isOpen_univ)
      C (hC.of_le (by simp)) K (hK ▸ Set.ordConnected_Icc) (D x) (fun _ ↦ 0) s hs
      ⟨hsU, Set.mem_univ _⟩ hz
      (((hD x).contDiffAt ((hU x).mem_nhds hsU)).continuousAt.continuousWithinAt)
      continuousWithinAt_const hode hzeroOde
  let S : Set K := {s | ∀ x, A.squareFamily Z s ∈ (chartAt Q x).source → D x s = 0}
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    let x := A.squareFamily Z s
    have hx : A.squareFamily Z s ∈ (chartAt Q x).source := mem_chart_source Q x
    have hsU := hKU s s.property x hx
    have hnear := hlocal x s s.property hsU (hs x hx)
    apply (eventually_nhds_subtype_iff K s
      (fun t ↦ ∀ y, A.squareFamily Z t ∈ (chartAt Q y).source → D y t = 0)).mpr
    filter_upwards [hnear, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((hU x).mem_nhds hsU)] with t ht htK htU
    intro y hy
    exact htransfer t htK x y (hsource x t htU) hy ht
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    have hnot : ¬ ∀ x, A.squareFamily Z s ∈ (chartAt Q x).source → D x s = 0 := hs
    push_neg at hnot
    obtain ⟨x, hx, hne⟩ := hnot
    have hsU := hKU s s.property x hx
    have hneNear : ∀ᶠ t in 𝓝 (s : ℝ), D x t ≠ 0 :=
      (((hD x).contDiffAt ((hU x).mem_nhds hsU)).continuousAt).eventually_ne hne
    apply (eventually_nhds_subtype_iff K s
      (fun t ↦ ¬ ∀ y, A.squareFamily Z t ∈ (chartAt Q y).source → D y t = 0)).mpr
    filter_upwards [mem_nhdsWithin_of_mem_nhds hneNear,
      mem_nhdsWithin_of_mem_nhds ((hU x).mem_nhds hsU)] with t ht htU
    intro h
    exact ht (h x (hsource x t htU))
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp (hK ▸ isPreconnected_Icc)
  have hSc : (⟨c, hc⟩ : K) ∈ S := by
    intro x hx
    exact htransfer c hc x0 x hx0 hx hzero
  have hAll : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨c, hc⟩, hSc⟩
  have h0K : (0 : ℝ) ∈ K := by rw [hK]; exact ⟨le_rfl, Real.sqrt_nonneg b⟩
  have h0S : (⟨0, h0K⟩ : K) ∈ S := by rw [hAll]; trivial
  have h0p : A.squareFamily Z 0 ∈ (chartAt Q p).source := by
    rw [A.square_at_zero]
    exact mem_chart_source Q p
  have hD0 : D p 0 = 0 := h0S p h0p
  let L : TangentSpace (𝓡 n) p →L[ℝ] Q := mfderiv (𝓡 n) (𝓡 n) (chartAt Q p) p
  have hline : HasDerivAt (fun u : ℝ ↦ Z + u • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hjet : HasDerivAt (fun u : ℝ ↦ ((chartAt Q p) p, L ((2 : ℝ) • (Z + u • W))))
      (0, L ((2 : ℝ) • W)) 0 :=
    (hasDerivAt_const 0 ((chartAt Q p) p)).prodMk
      (L.hasFDerivAt.comp_hasDerivAt 0 (hline.const_smul (2 : ℝ)))
  have heq : (fun u ↦ P p (0, u)) =
      (fun u : ℝ ↦ ((chartAt Q p) p, L ((2 : ℝ) • (Z + u • W)))) := by
    funext u
    change ((chartAt Q p) (A.squareFamily (Z + u • W) 0),
      (mfderiv (𝓡 n) (𝓡 n) (chartAt Q p) (A.squareFamily (Z + u • W) 0))
        (curveVelocity (n := n) (A.squareFamily (Z + u • W)) 0 : Q)) = _
    rw [lExponentialFamily_initial_velocity, A.square_at_zero]
    rfl
  have hj : (0, L ((2 : ℝ) • W)) = (0 : Q × Q) := by
    rw [← hD0]
    change (0, L ((2 : ℝ) • W)) = deriv (fun u ↦ P p (0, u)) 0
    rw [heq, hjet.deriv]
  have hLzero : L ((2 : ℝ) • W) = L 0 := by
    exact (show L ((2 : ℝ) • W) = 0 from congrArg Prod.snd hj).trans (map_zero L).symm
  have hWzero : (2 : ℝ) • W = 0 :=
    (mdifferentiable_chart (I := 𝓡 n) p).mfderiv_bijective (mem_chart_source Q p) |>.injective hLzero
  exact (smul_eq_zero.mp hWzero).resolve_left (by norm_num)

end PoincareConjecture.Proofs.M09
