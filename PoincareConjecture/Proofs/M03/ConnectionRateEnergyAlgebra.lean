import PoincareConjecture.Proofs.M03.ScalarEnergyComparison
import PoincareConjecture.Proofs.M03.ConnectionNativeTime
import PoincareConjecture.Proofs.M03.MetricGradientEvolution
import PoincareConjecture.Proofs.M03.ConnectionRateRicciSmoothness
import PoincareConjecture.Proofs.M03.CurvatureFluxAlgebra
import PoincareConjecture.Proofs.M03.CurvatureFluxDivergenceAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Bounds









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set Filter

universe u

namespace PoincareConjecture.Proofs.M03



theorem add_young_and_reaction_bound
    {L R X Y Z ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hL : L ≤ ε * X + (C / ε) * Y)
    (hR : R ≤ C * Z) :
    L + R ≤ ε * X + (C / ε + C) * (Y + Z) := by
  calc
    L + R ≤ (ε * X + (C / ε) * Y) + C * Z := add_le_add hL hR
    _ ≤ ε * X + (C / ε + C) * (Y + Z) := by
      have hCY : 0 ≤ C * Y := mul_nonneg hC hY
      have hCεZ : 0 ≤ (C / ε) * Z :=
        mul_nonneg (div_nonneg hC hε.le) hZ
      nlinarith

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_inverse_and_lowered_frame_terminal_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ t ∈ Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {Q : Set M} (hQ : IsCompact Q)
    (hQframe : Q ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
    let H := fun (s : ℝ) (x : M) (i j : Fin n) =>
      (ContinuousLinearMap.inverse (G s x) (EuclideanSpace.proj j)) i
    let L := fun (k : ℕ) (s : ℝ) (α : Fin (k + 4) → Fin n) (x : M) =>
      (F.metric s).inner x
        (curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
          (fun j : Fin (k + 3) => E (α j.castSucc)) x)
        (E (α (Fin.last (k + 3))) x)
    (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ico a T, ∀ x ∈ Q,
      ∀ i j : Fin n, |H s x i j| ≤ B) ∧
    (∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ico a T, ∀ x ∈ Q,
      ∀ α : Fin (k + 4) → Fin n, |L k s α x| ≤ B) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let G := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x ((F.metric s).inner x)
  let H := fun (s : ℝ) (x : M) (i j : Fin n) =>
    (ContinuousLinearMap.inverse (G s x) (EuclideanSpace.proj j)) i
  let K := fun k s => curvatureOnFields_iteratedCovariantDerivative (F.connection s) k
  let L := fun k s (α : Fin (k + 4) → Fin n) x =>
    (F.metric s).inner x (K k s (fun j : Fin (k + 3) => E (α j.castSucc)) x)
      (E (α (Fin.last (k + 3))) x)
  change (∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ i j, |H s x i j| ≤ B) ∧
    (∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Ico a T, ∀ x ∈ Q, ∀ α, |L k s α x| ≤ B)
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hold {s : ℝ} (hs : s ∈ Ico a T) : s ∈ Ico 0 T :=
    ⟨ha.le.trans hs.1, hs.2⟩
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hEvalue {x : M} (hx : x ∈ e.baseSet) (i : Fin n) :
      E i x = e.symmL ℝ x (cb i) := by
    dsimp only [E]
    rw [e.localFrame_apply_of_mem_baseSet cb hx]
    simp only [Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply]
    exact (Trivialization.symmL_apply (R := ℝ) e hx (cb i)).symm
  have hGeq (s : ℝ) {x : M} (hx : x ∈ e.baseSet) (v w : V) :
      G s x v w = (F.metric s).inner x (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx v,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
  obtain ⟨c0, C0, hc0, hC0, hframe0⟩ := exists_pos_uniform_metric_frame_bounds
    (F.smooth.mono (Set.prod_mono (singleton_subset_iff.mpr h0) subset_rfl))
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) x0 hQ hQframe
  let lam := 2 * (n : ℝ) * max C 0
  let d := Real.exp (-(lam * T)) * c0
  let D := Real.exp (lam * T) * C0
  have hd : 0 < d := mul_pos (Real.exp_pos _) hc0
  have hD : 0 < D := mul_pos (Real.exp_pos _) hC0
  let W := Real.sqrt D
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hcomparison := (metric_endpoint_control_of_curvature_bound hT F hRm).1
  have hframe {s : ℝ} (hs : s ∈ Ico 0 T) {x : M} (hx : x ∈ Q) (v : V) :
      d * ‖v‖ ^ 2 ≤ (F.metric s).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ∧
      (F.metric s).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ≤ D * ‖v‖ ^ 2 := by
    have hzero := hframe0 0 (mem_singleton 0) x hx v
    have hsmetric := hcomparison s hs x (e.symmL ℝ x v)
    constructor
    · calc
        _ = Real.exp (-(lam * T)) * (c0 * ‖v‖ ^ 2) := by dsimp only [d]; ring
        _ ≤ Real.exp (-(lam * T)) * (F.metric 0).inner x
            (e.symmL ℝ x v) (e.symmL ℝ x v) :=
          mul_le_mul_of_nonneg_left hzero.1 (Real.exp_pos _).le
        _ ≤ _ := hsmetric.1
    · calc
        _ ≤ Real.exp (lam * T) * (F.metric 0).inner x
            (e.symmL ℝ x v) (e.symmL ℝ x v) := hsmetric.2
        _ ≤ Real.exp (lam * T) * (C0 * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hzero.2 (Real.exp_pos _).le
        _ = D * ‖v‖ ^ 2 := by dsimp only [D]; ring
  have hframeNorm {s : ℝ} (hs : s ∈ Ico 0 T) {x : M} (hx : x ∈ Q) (i : Fin n) :
      (F.metric s).tangentNorm x (E i x) ≤ W := by
    have hh := (hframe hs hx (cb i)).2
    have hcb : ‖cb i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
    rw [hcb, one_pow, mul_one] at hh
    rw [hEvalue (hQframe hx), RiemannianMetric.tangentNorm]
    exact Real.sqrt_le_sqrt hh
  constructor
  · refine ⟨d⁻¹, inv_nonneg.mpr hd.le, ?_⟩
    intro s hs x hx i j
    have hpos : (G s x).IsInvertible := by
      apply isInvertible_bilinear_of_pos
      intro v hv
      rw [hGeq s (hQframe hx)]
      exact (mul_pos hd (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le
        (hframe (hold hs) hx v).1
    let v := ContinuousLinearMap.inverse (G s x) (EuclideanSpace.proj j)
    have hinv : G s x v = EuclideanSpace.proj j := hpos.self_apply_inverse _
    have hdiag : G s x v v = v j := by rw [hinv]; rfl
    have hnorm : d * ‖v‖ ^ 2 ≤ ‖v‖ := by
      have hh := (hframe (hold hs) hx v).1
      rw [← hGeq s (hQframe hx), hdiag] at hh
      exact hh.trans ((le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j))
    have hv : ‖v‖ ≤ d⁻¹ := by
      by_cases hz : ‖v‖ = 0
      · rw [hz]
        exact inv_nonneg.mpr hd.le
      · have hvpos := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hz)
        have hmul : (d * ‖v‖) * ‖v‖ ≤ 1 * ‖v‖ := by nlinarith only [hnorm]
        have hdv : d * ‖v‖ ≤ 1 := (mul_le_mul_iff_left₀ hvpos).mp hmul
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hd).mpr (by nlinarith only [hdv])
    exact (show |v i| ≤ ‖v‖ from by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i).trans hv
  · intro k
    obtain ⟨A, hA, hAbound⟩ := ricciFlow_iteratedCurvature_terminal_bound hT F hRm ha haT k
    refine ⟨A * W ^ (k + 4), mul_nonneg hA (pow_nonneg hW _), ?_⟩
    intro s hs x hx α
    have hb := abs_curvature_iterated_pairing_le_orthonormal_energy
      (F.connection s) k e.open_baseSet (fun j => E (α j.castSucc))
      (fun j => hE (α j.castSucc)) (hQframe hx) (E (α (Fin.last (k + 3))) x)
    have hp : (∏ j : Fin (k + 3), (F.metric s).tangentNorm x (E (α j.castSucc) x)) ≤
        W ^ (k + 3) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        RiemannianMetric.tangentNorm] using
        (Finset.prod_le_prod
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin (k + 3)))) => Real.sqrt_nonneg _)
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin (k + 3)))) =>
            hframeNorm (hold hs) hx (α j.castSucc)))
    have hAp := hAbound s hs x
    have hp0 : 0 ≤ ∏ j : Fin (k + 3), (F.metric s).tangentNorm x (E (α j.castSucc) x) :=
      Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
    calc
      |L k s α x| ≤ _ := hb
      _ ≤ A * W ^ (k + 3) * W :=
        mul_le_mul (mul_le_mul hAp hp hp0 hA)
          (hframeNorm (hold hs) hx (α (Fin.last (k + 3))))
          (Real.sqrt_nonneg _) (mul_nonneg hA (pow_nonneg hW _))
      _ = A * W ^ (k + 4) := by rw [pow_succ W (k + 3)]; ring

end PoincareConjecture.Proofs.M03

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set Filter

namespace PoincareConjecture.Proofs.M03

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 3000 in

theorem ricciFlow_metric_first_coordinate_jet_terminal_control
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ t ∈ Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x0).target) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
      (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧
      (∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
        ‖fderiv ℝ (G s i j) z‖ ≤ B) ∧
      (∀ s ∈ Ico a T, ∀ t ∈ Ico a T,
        ∀ z ∈ K, ∀ i j : Fin n,
          ‖fderiv ℝ (G t i j) z - fderiv ℝ (G s i j) z‖ ≤ L * |t - s|) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let Q := c.symm '' K
  let N := fun s (P W : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection W y (P y)
  let R := fun s (P W Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields P W Z y
  let D1 := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let energy := fun s y =>
    let b := (F.metric s).orthonormalBasis y
    let ext := fun i => FiberBundle.extend V (b i)
    let kb := fun γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y)) =>
      D1 s (ext (γ 0)) (ext (γ 1)) (ext (γ 2)) (ext (γ 3)) y
    ∑ γ, (F.metric s).inner y (kb γ) (kb γ)
  let Gamma := fun s y (i j l : Fin n) => theta l y (N s (E i) (E j) y)
  let gpair := fun s i j y => (F.metric s).inner y (E i y) (E j y)
  let ric := fun s i j y => (F.connection s).ricci y (E i y) (E j y)
  let G := fun s (i j : Fin n) z => gpair s i j (c.symm z)
  have htime {s : ℝ} (hs : s ∈ Ico a T) : s ∈ interior (Ico 0 T) := by
    rw [interior_Ico]
    exact ⟨ha.trans_le hs.1, hs.2⟩
  have hold {s : ℝ} (hs : s ∈ Ico a T) : s ∈ Ico 0 T :=
    ⟨ha.le.trans hs.1, hs.2⟩
  have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hQ : IsCompact Q := hK.image_of_continuousOn (c.continuousOn_symm.mono hKchart)
  have hQbase : Q ⊆ e.baseSet := by
    rintro y ⟨z, hz, rfl⟩
    exact hbase (hKchart hz)
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hEframe (i : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      E i y = e.symmL ℝ y (EuclideanSpace.single i 1) := by
    calc
      E i y = e.basisAt cb hy i := e.localFrame_apply_of_mem_baseSet cb hy
      _ = e.symm y (EuclideanSpace.single i 1) := by
        simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          Trivialization.linearEquivAt_symm_apply]
      _ = e.symmL ℝ y (EuclideanSpace.single i 1) := (e.symmL_apply hy _).symm
  have hpair (s : ℝ) (hs : s ∈ Ico 0 T) (i j : Fin n) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (gpair s i j) e.baseSet := by
    exact (contMDiffOn_family_metric_pair F.smooth (E i) (E j) (hE i) (hE j)).comp
      (contMDiffOn_const.prodMk contMDiffOn_id) (fun y hy => ⟨hs, hy⟩)
  have hcs {z : V} (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, V) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
      (c.open_target.mem_nhds hz)
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet)
      {z : V} (hz : z ∈ c.target) (l : Fin n) :
      fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single l 1) =
        mvfderiv (𝓡 n) f (c.symm z) (E l (c.symm z)) := by
    have he := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
      (c.map_target hz)
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
      mfderivWithin_univ] at he
    change e.symmL ℝ (c.symm z) = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm
      (c (c.symm z)) at he
    rw [c.right_inv hz] at he
    rw [hEframe l (hbase hz), ← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single l 1) = _
    erw [mvfderiv_comp_apply z
      ((hf.contMDiffAt (e.open_baseSet.mem_nhds (hbase hz))).mdifferentiableAt (by simp))
      ((hcs hz).mdifferentiableAt (by simp)) (EuclideanSpace.single l 1), ← he]
    rfl
  have hnonneg (g : RiemannianMetric n M) (y : M) (v : TangentSpace (𝓡 n) y) :
      0 ≤ g.inner y v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos y v hv).le
  have hinner (g : RiemannianMetric n M) (y : M) (v w : TangentSpace (𝓡 n) y) :
      |g.inner y v w| ≤ g.tangentNorm y v * g.tangentNorm y w := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (v : TangentSpace (𝓡 n) y) : g.tangentNorm y v = ‖v‖ := by
      rw [RiemannianMetric.tangentNorm,
        show g.inner y v v = ‖v‖ ^ 2 from real_inner_self_eq_norm_sq v,
        Real.sqrt_sq (norm_nonneg _)]
    rw [hn, hn]
    exact abs_real_inner_le_norm v w
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hsum0 : ContinuousOn (fun y => ∑ i : Fin n, gpair 0 i i y) Q :=
    continuousOn_finsetSum _ (fun i _ => (hpair 0 h0 i i).continuousOn.mono hQbase)
  obtain ⟨A0, hA0⟩ := hQ.bddAbove_image hsum0
  let rate0 := 2 * (n : ℝ) * max C 0
  let W := Real.sqrt (Real.exp (rate0 * T) * max A0 0)
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hmetric := (metric_endpoint_control_of_curvature_bound hT F hRm).1
  have hEnorm (s : ℝ) (hs : s ∈ Ico a T) (y : M) (hy : y ∈ Q) (i : Fin n) :
      (F.metric s).tangentNorm y (E i y) ≤ W := by
    have hdiag0 : (F.metric 0).inner y (E i y) (E i y) ≤ max A0 0 := by
      calc
        _ ≤ ∑ j : Fin n, gpair 0 j j y :=
          Finset.single_le_sum (fun j _ => hnonneg _ _ _) (Finset.mem_univ i)
        _ ≤ A0 := hA0 (mem_image_of_mem _ hy)
        _ ≤ max A0 0 := le_max_left _ _
    apply Real.sqrt_le_sqrt
    exact ((hmetric s (hold hs) y (E i y)).2).trans
      (mul_le_mul_of_nonneg_left hdiag0 (Real.exp_pos _).le)
  obtain ⟨BG, LG, hBG, hLG, hGamma, _, _⟩ :=
    ricciFlow_connection_frame_terminal_control hT F hRm ha haT x0 hQ hQbase
  change ∀ s ∈ Ico a T, ∀ y ∈ Q, ∀ i j l : Fin n,
    |Gamma s y i j l| ≤ BG at hGamma
  let NC := (n : ℝ) * BG * W
  have hNC : 0 ≤ NC := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hBG) hW
  have hNnorm (s : ℝ) (hs : s ∈ Ico a T) (y : M) (hy : y ∈ Q) (i j : Fin n) :
      (F.metric s).tangentNorm y (N s (E i) (E j) y) ≤ NC := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    have hn (v : TangentSpace (𝓡 n) y) : (F.metric s).tangentNorm y v = ‖v‖ := by
      rw [RiemannianMetric.tangentNorm,
        show (F.metric s).inner y v v = ‖v‖ ^ 2 from real_inner_self_eq_norm_sq v,
        Real.sqrt_sq (norm_nonneg _)]
    have hr : N s (E i) (E j) y = ∑ l : Fin n, Gamma s y i j l • E l y :=
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb) (hQbase hy)
    rw [hn, hr]
    calc
      _ ≤ ∑ l : Fin n, ‖Gamma s y i j l • E l y‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin n, BG * W := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hGamma s hs y hy i j l)
          (by rw [← hn]; exact hEnorm s hs y hy l) (norm_nonneg _) hBG
      _ = NC := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; dsimp only [NC]; ring
  obtain ⟨Qa, hQa, _, _, hQaBound⟩ :=
    ricciFlow_curvature_derivative_energy_terminal_bound hT F hRm ha haT
  let gradRate := 96 * ((n : ℝ) + 1) ^ 3 * max C 0
  let W1 := Real.sqrt (Qa * Real.exp (gradRate * (T - a)))
  have hW1 : 0 ≤ W1 := Real.sqrt_nonneg _
  change ∀ s ∈ Ico a T, ∀ y : M,
    energy s y ≤ Qa * Real.exp (gradRate * (T - a)) at hQaBound
  have henergy (s : ℝ) (hs : s ∈ Ico a T) (y : M) :
      Real.sqrt (energy s y) ≤ W1 := Real.sqrt_le_sqrt (hQaBound s hs y)
  let RC := (n : ℝ) * W1 * W ^ 3 + 2 * ((n : ℝ) * max C 0 * NC * W)
  have hRC : 0 ≤ RC := by dsimp only [RC]; positivity
  have hRicci (s : ℝ) (hs : s ∈ Ico a T) (y : M)
      (v w : TangentSpace (𝓡 n) y) :
      |(F.connection s).ricci y v w| ≤ (n : ℝ) * max C 0 *
        (F.metric s).tangentNorm y v * (F.metric s).tangentNorm y w := by
    apply (abs_ricci_le_curvatureTensorNorm (F.connection s) y v w).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          ((hRm s (hold hs) y).trans (le_max_left _ _)) (Nat.cast_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hRicSpace (s : ℝ) (hs : s ∈ Ico a T) (i j : Fin n) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ric s i j) e.baseSet := by
    intro y hy
    exact (connection_rate_ricci_pair_smooth F (htime hs) e.open_baseSet
      (E i) (E j) (hE i) (hE j) hy).contMDiffWithinAt
  have hRicDeriv (s : ℝ) (hs : s ∈ Ico a T) (y : M) (hy : y ∈ Q)
      (l i j : Fin n) : |mvfderiv (𝓡 n) (ric s i j) y (E l y)| ≤ RC := by
    let g := F.metric s
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let D := F.connection s
    let b := g.orthonormalBasis y
    let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) y))
    let ext := fun r : ι => FiberBundle.extend V (b r)
    have hrepr (v : TangentSpace (𝓡 n) y) (r : ι) :
        b.toBasis.repr v r = g.inner y v (b r) := by
      rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      exact g.symm y _ _
    have hb (r : ι) : g.tangentNorm y (b r) = 1 := by
      change Real.sqrt (inner ℝ (b r) (b r)) = 1
      rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
      norm_num
    have hterm (r : ι) : |g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r)| ≤
        W1 * W ^ 3 := by
      obtain ⟨S, hS, hExt⟩ := FiberBundle.exists_contMDiffOn_extend
        (k := ∞) (𝓡 n) V (b r)
      obtain ⟨U, hUS, hU, hyU⟩ := mem_nhds_iff.mp
        (inter_mem hS (e.open_baseSet.mem_nhds (hQbase hy)))
      have hEU (q : Fin n) : ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E q)) U :=
        (hE q).mono (fun _ hz => (hUS hz).2)
      have hextU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
          (T% (ext r)) U := hExt.mono (fun _ hz => (hUS hz).1)
      have hh := abs_curvature_derivative_pairing_le_orthonormal_energy D hU
        (E l) (ext r) (E i) (E j) (hEU l) hextU (hEU i) (hEU j) hyU (b r)
      change |g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r)| ≤
        Real.sqrt (energy s y) * g.tangentNorm y (E l y) *
          g.tangentNorm y (ext r y) * g.tangentNorm y (E i y) *
            g.tangentNorm y (E j y) * g.tangentNorm y (b r) at hh
      have hext : ext r y = b r := FiberBundle.extend_apply_self V (b r)
      rw [hext, hb, mul_one, mul_one] at hh
      calc
        _ ≤ Real.sqrt (energy s y) * g.tangentNorm y (E l y) *
            g.tangentNorm y (E i y) * g.tangentNorm y (E j y) := hh
        _ ≤ W1 * W * W * W := by
          gcongr
          all_goals first
          | exact Real.sqrt_nonneg _
          | exact henergy s hs y
          | exact hEnorm s hs y hy l
          | exact hEnorm s hs y hy i
          | exact hEnorm s hs y hy j
        _ = W1 * W ^ 3 := by ring
    have hdim : Fintype.card ι = n := by
      dsimp only [ι]
      rw [Fintype.card_fin, VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) y,
        finrank_euclideanSpace_fin]
    have htrace := ricci_covariant_derivative_eq_sum_basis D e.open_baseSet
      (E l) (E i) (E j) (hE l) (hE i) (hE j) (hQbase hy) b.toBasis
    change mvfderiv (𝓡 n) (ric s i j) y (E l y) -
      D.ricci y (N s (E l) (E i) y) (E j y) -
      D.ricci y (E i y) (N s (E l) (E j) y) =
        ∑ r : ι, b.toBasis.repr (D1 s (E l) (ext r) (E i) (E j) y) r at htrace
    simp_rw [hrepr] at htrace
    have hsum : |∑ r : ι, g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r)| ≤
        (n : ℝ) * W1 * W ^ 3 := by
      calc
        _ ≤ ∑ r : ι, |g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r : ι, W1 * W ^ 3 := Finset.sum_le_sum (fun r _ => hterm r)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul]; ring
    have hc1 : |D.ricci y (N s (E l) (E i) y) (E j y)| ≤
        (n : ℝ) * max C 0 * NC * W := by
      apply (hRicci s hs y _ _).trans
      gcongr
      all_goals first
      | exact Real.sqrt_nonneg _
      | exact hNnorm s hs y hy l i
      | exact hEnorm s hs y hy j
    have hc2 : |D.ricci y (E i y) (N s (E l) (E j) y)| ≤
        (n : ℝ) * max C 0 * NC * W := by
      calc
        _ ≤ (n : ℝ) * max C 0 * (F.metric s).tangentNorm y (E i y) *
            (F.metric s).tangentNorm y (N s (E l) (E j) y) := hRicci s hs y _ _
        _ ≤ (n : ℝ) * max C 0 * W * NC := by
          gcongr
          all_goals first
          | exact Real.sqrt_nonneg _
          | exact hEnorm s hs y hy i
          | exact hNnorm s hs y hy l j
        _ = _ := by ring
    have heq : mvfderiv (𝓡 n) (ric s i j) y (E l y) =
        (∑ r : ι, g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r)) +
          D.ricci y (N s (E l) (E i) y) (E j y) +
          D.ricci y (E i y) (N s (E l) (E j) y) := by
      linarith only [htrace]
    rw [heq]
    calc
      _ ≤ (|(∑ r : ι, g.inner y (D1 s (E l) (ext r) (E i) (E j) y) (b r))| +
          |D.ricci y (N s (E l) (E i) y) (E j y)|) +
          |D.ricci y (E i y) (N s (E l) (E j) y)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ RC := by dsimp only [RC]; linarith only [hsum, hc1, hc2]
  have hop (A : V →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
      (hb : ∀ l : Fin n, |A (EuclideanSpace.single l 1)| ≤ B) :
      ‖A‖ ≤ (n : ℝ) * B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
    intro v
    have hv : v = ∑ l : Fin n, v l • EuclideanSpace.single l 1 := by
      let b := PiLp.basisFun 2 ℝ (Fin n)
      simpa only [b, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr v).symm
    calc
      ‖A v‖ = ‖∑ l : Fin n, v l • A (EuclideanSpace.single l 1)‖ := by
        conv_lhs => rw [hv]
        simp only [map_sum, map_smul]
      _ ≤ ∑ l : Fin n, ‖v l • A (EuclideanSpace.single l 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin n, ‖v‖ * B := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v l)
          (hb l) (abs_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * B * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  let GB := 2 * NC * W
  let LB := 2 * RC
  have hGB : 0 ≤ GB := mul_nonneg (mul_nonneg (by norm_num) hNC) hW
  have hLB : 0 ≤ LB := mul_nonneg (by norm_num) hRC
  refine ⟨(n : ℝ) * GB, (n : ℝ) * LB,
    mul_nonneg (Nat.cast_nonneg _) hGB, mul_nonneg (Nat.cast_nonneg _) hLB, ?_, ?_⟩
  · intro s hs z hz i j
    apply hop _ GB hGB
    intro l
    rw [hchart (gpair s i j) (hpair s (hold hs) i j) (hKchart hz) l]
    have hy : c.symm z ∈ Q := mem_image_of_mem _ hz
    have hemd (r : Fin n) := ((hE r).contMDiffAt
      (e.open_baseSet.mem_nhds (hQbase hy))).mdifferentiableAt (by simp)
    rw [(F.connection s).mvfderiv_inner (E l) (E i) (E j) (hemd i) (hemd j)]
    apply (abs_add_le _ _).trans
    have h1 := (hinner (F.metric s) (c.symm z) (N s (E l) (E i) (c.symm z))
      (E j (c.symm z))).trans (mul_le_mul (hNnorm s hs _ hy l i)
        (hEnorm s hs _ hy j) (Real.sqrt_nonneg _) hNC)
    have h2 := (hinner (F.metric s) (c.symm z) (E i (c.symm z))
      (N s (E l) (E j) (c.symm z))).trans (mul_le_mul (hEnorm s hs _ hy i)
        (hNnorm s hs _ hy l j) (Real.sqrt_nonneg _) hW)
    dsimp only [GB]
    nlinarith only [h1, h2]
  · intro s hs t ht z hz i j
    have hcomp (l : Fin n) : |(fderiv ℝ (G t i j) z - fderiv ℝ (G s i j) z)
        (EuclideanSpace.single l 1)| ≤ LB * |t - s| := by
      let f := fun r => fderiv ℝ (G r i j) z (EuclideanSpace.single l 1)
      let df := fun r => fderiv ℝ (fun w => -2 * ric r i j (c.symm w)) z
        (EuclideanSpace.single l 1)
      have hd (r : ℝ) (hr : r ∈ Ico a T) : HasDerivAt f (df r) r := by
        have hzext : z ∈ (extChartAt (𝓡 n) x0).target := by
          simpa only [extChartAt_target, (𝓡 n).range_eq_univ,
            modelWithCornersSelf_coe_symm, preimage_id, inter_univ] using hKchart hz
        have hzx : (extChartAt (𝓡 n) x0).symm z ∈ e.baseSet := by
          simpa only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
            Function.comp_def, id_eq] using hbase (hKchart hz)
        convert hasDerivAt_ricciFlow_metric_spatial_derivative F (htime hr) e.open_baseSet
          (E i) (E j) (hE i) (hE j) x0 hzext hzx (EuclideanSpace.single l 1) using 1 <;>
          simp only [f, df, G, gpair, ric, c, V, extChartAt_coe_symm,
            modelWithCornersSelf_coe_symm, Function.comp_def, id_eq]
        funext s
        rfl
      have hdf (r : ℝ) (hr : r ∈ Ico a T) : ‖df r‖ ≤ LB := by
        have hdiff : DifferentiableAt ℝ (fun w => ric r i j (c.symm w)) z :=
          (((hRicSpace r hr i j).contMDiffAt (e.open_baseSet.mem_nhds
            (hbase (hKchart hz)))).comp z (hcs (hKchart hz))).contDiffAt.differentiableAt
              (by simp)
        dsimp only [df]
        rw [fderiv_const_mul hdiff, smul_apply, smul_eq_mul,
          Real.norm_eq_abs, abs_mul, hchart (ric r i j) (hRicSpace r hr i j) (hKchart hz) l]
        rw [show |(-2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left
          (hRicDeriv r hr _ (mem_image_of_mem _ hz) l i j) (by norm_num)
      have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r hr => (hd r hr).hasDerivWithinAt) hdf (convex_Ico a T) hs ht
      simpa only [f, sub_apply, Real.norm_eq_abs] using hh
    have hh := hop (fderiv ℝ (G t i j) z - fderiv ℝ (G s i j) z)
      (LB * |t - s|) (mul_nonneg hLB (abs_nonneg _)) hcomp
    simpa only [mul_assoc] using hh

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

theorem norm_iteratedFDeriv_mul_le_of_open_bounds
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (q : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfb : ∀ p ≤ q, ‖iteratedFDeriv ℝ p f x‖ ≤ A)
    (hgb : ∀ p ≤ q, ‖iteratedFDeriv ℝ p g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ q (fun z => f z * g z) x‖ ≤ (2 : ℝ) ^ q * A * B := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl q)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at h
  calc
    _ ≤ ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (q - i) g x‖ := h
    _ ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (hfb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (Nat.cast_nonneg _)
      · exact hgb (q - i) (Nat.sub_le _ _)
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) hA
    _ = (2 : ℝ) ^ q * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hc : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) = (2 : ℝ) ^ q := by
        exact_mod_cast Nat.sum_range_choose q
      rw [hc]

theorem norm_iteratedFDeriv_succ_le_of_coordinate_bounds
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (_hf : ContDiffOn ℝ ∞ f U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hderiv : ∀ y ∈ U, ∀ i : Fin n,
      fderiv ℝ f y (EuclideanSpace.single i 1) = b i y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (q : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i : Fin n, ‖iteratedFDeriv ℝ q (b i) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ (n : ℝ) * B := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let S := fun i : Fin n => (ContinuousLinearMap.id ℝ ℝ).smulRight
    (EuclideanSpace.proj i : V →L[ℝ] ℝ)
  have hproj (i : Fin n) : ‖(EuclideanSpace.proj i : V →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖v i‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using PiLp.norm_apply_le v i
  have hS (i : Fin n) : ‖S i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro r
    change ‖r • (EuclideanSpace.proj i : V →L[ℝ] ℝ)‖ ≤ 1 * ‖r‖
    rw [norm_smul, one_mul]
    exact (mul_le_mul_of_nonneg_left (hproj i) (norm_nonneg r)).trans_eq (mul_one _)
  have heq : fderiv ℝ f =ᶠ[𝓝 x] fun y => ∑ i : Fin n, S i (b i y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    apply ContinuousLinearMap.ext
    intro v
    have hv : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    calc
      fderiv ℝ f y v = fderiv ℝ f y (∑ i : Fin n, v i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ f y) hv.symm
      _ = ∑ i : Fin n, v i * b i y := by simp only [map_sum, map_smul, hderiv y hy,
        smul_eq_mul]
      _ = (∑ i : Fin n, S i (b i y)) v := by
        simp only [sum_apply, S, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul, mul_comm]
        rfl
  rw [← norm_iteratedFDeriv_fderiv, (heq.iteratedFDeriv ℝ q).eq_of_nhds]
  have hsmooth (i : Fin n) : ContDiffAt ℝ ∞ (fun y => S i (b i y)) x :=
    (S i).contDiff.contDiffAt.comp x ((hb i).contDiffAt (hU.mem_nhds hx))
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    (hsmooth i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
  calc
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ q (fun y => S i (b i y)) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, B := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖S i‖ * ‖iteratedFDeriv ℝ q (b i) x‖ :=
          (S i).norm_iteratedFDeriv_comp_left
            ((hb i).contDiffAt (hU.mem_nhds hx))
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl q)
        _ ≤ ‖S i‖ * B := mul_le_mul_of_nonneg_left (hbound i) (norm_nonneg (S i))
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right (hS i) hB
        _ = B := one_mul B
    _ = (n : ℝ) * B := by simp

theorem ricciFlow_inverse_and_lowered_coordinate_jets_of_connection_jets
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ s ∈ Ico 0 T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x0).target)
    (m : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let Gamma := fun (s : ℝ) (i j l : Fin n) (z : V) =>
      theta l (c.symm z)
        ((F.connection s).connection (E j) (c.symm z) (E i (c.symm z)))
    let G := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x ((F.metric s).inner x)
    let H := fun (s : ℝ) (i j : Fin n) (z : V) =>
      (G s (c.symm z)).inverse (EuclideanSpace.proj j) i
    let L := fun (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
      (F.metric s).inner (c.symm z)
        (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
          (fun j : Fin (r + 3) => E (alpha j.castSucc)) (c.symm z))
        (E (alpha (Fin.last (r + 3))) (c.symm z))
    (∃ A : ℝ, 0 ≤ A ∧
      ∀ q < m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
        ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ A) →
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ q (H s i j) z‖ ≤ B) ∧
    (∀ r : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K,
        ∀ alpha : Fin (r + 4) → Fin n,
          ‖iteratedFDeriv ℝ q (L r s alpha) z‖ ≤ B) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let Gamma := fun (s : ℝ) (i j l : Fin n) (z : V) =>
    theta l (c.symm z)
      ((F.connection s).connection (E j) (c.symm z) (E i (c.symm z)))
  let G := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x ((F.metric s).inner x)
  let H := fun (s : ℝ) (i j : Fin n) (z : V) =>
    (G s (c.symm z)).inverse (EuclideanSpace.proj j) i
  let L := fun (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
    (F.metric s).inner (c.symm z)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)) (c.symm z))
      (E (alpha (Fin.last (r + 3))) (c.symm z))
  change (∃ A : ℝ, 0 ≤ A ∧
      ∀ q < m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
        ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ A) →
    (∃ B : ℝ, 0 ≤ B ∧
      ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ q (H s i j) z‖ ≤ B) ∧
    (∀ r : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ alpha : Fin (r + 4) → Fin n,
        ‖iteratedFDeriv ℝ q (L r s alpha) z‖ ≤ B)
  rintro ⟨A, hA, hAbound⟩
  have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  let Q := c.symm '' K
  have hQ : IsCompact Q := hK.image_of_continuousOn (c.continuousOn_symm.mono hKchart)
  have hQbase : Q ⊆ e.baseSet := by
    rintro y ⟨z, hz, rfl⟩
    exact hbase (hKchart hz)
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) :
      ContDiffOn ℝ ∞ (fun z => f (c.symm z)) c.target :=
    (hf.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
      (fun z hz => hbase hz)).contDiffOn
  have hfamily (s : ℝ) : RiemannianMetric.IsSmoothFamilyOn
      (fun _ : ℝ => F.metric s) Set.univ :=
    ((F.metric s).contMDiff.comp contMDiff_snd).contMDiffOn
  have hGammaSmooth (s : ℝ) (i j l : Fin n) :
      ContDiffOn ℝ ∞ (Gamma s i j l) c.target := by
    apply hchart (fun y => theta l y ((F.connection s).connection (E j) y (E i y)))
    exact contMDiffOn_localFrameCoeff cb e.open_baseSet subset_rfl
      ((F.connection s).contMDiffOn_connection_apply e.open_baseSet
        (E i) (E j) (hE i) (hE j)) l
  have hHSmooth (s : ℝ) (i j : Fin n) :
      ContDiffOn ℝ ∞ (H s i j) c.target := by
    have hInv : ContMDiffOn (𝓡 n) 𝓘(ℝ, (V →L[ℝ] ℝ) →L[ℝ] V) ∞
        (fun y => (G s y).inverse) e.baseSet :=
      (contMDiffOn_family_metric_frame_inverse (hfamily s) x0).2.2.comp
        (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
          (fun y : M => ((0 : ℝ), y)) e.baseSet from
          contMDiffOn_const.prodMk contMDiffOn_id)
        (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
    apply hchart (fun y => (EuclideanSpace.proj i : V →L[ℝ] ℝ)
      ((G s y).inverse (EuclideanSpace.proj j)))
    exact (EuclideanSpace.proj i : V →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
      (hInv.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hLSmooth (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) :
      ContDiffOn ℝ ∞ (L r s alpha) c.target := by
    apply hchart (fun y => (F.metric s).inner y
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)) y)
      (E (alpha (Fin.last (r + 3))) y))
    exact (contMDiffOn_family_metric_pair (hfamily s)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)))
      (E (alpha (Fin.last (r + 3))))
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection s)
        e.open_baseSet r _ (fun j => hE (alpha j.castSucc)))
      (hE (alpha (Fin.last (r + 3))))).comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
  have hHderiv (s : ℝ) (z : V) (hz : z ∈ c.target) (i j k : Fin n) :
      fderiv ℝ (H s j k) z (EuclideanSpace.single i 1) =
        -(∑ p : Fin n, (Gamma s i p j z * H s p k z +
          Gamma s i p k z * H s j p z)) :=
    metric_inverse_covariant_derivative_coordinates (F.connection s) x0 z hz i j k
  have hLderiv (r : ℕ) (s : ℝ) (z : V) (hz : z ∈ c.target)
      (i : Fin n) (alpha : Fin (r + 4) → Fin n) :
      fderiv ℝ (L r s alpha) z (EuclideanSpace.single i 1) =
        L (r + 1) s (Fin.cons i alpha) z +
          ∑ j : Fin (r + 4), ∑ p : Fin n,
            Gamma s i (alpha j) p z * L r s (Function.update alpha j p) z :=
    curvature_iterated_lowered_frame_coordinate_derivative
      (F.connection s) x0 r z hz i alpha
  have hsum {N : ℕ} (f : Fin N → V → ℝ)
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) c.target)
      (z : V) (hz : z ∈ c.target) (q : ℕ) (B : ℝ)
      (hb : ∀ i, ‖iteratedFDeriv ℝ q (f i) z‖ ≤ B) :
      ‖iteratedFDeriv ℝ q (fun y => ∑ i, f i y) z‖ ≤ (N : ℝ) * B := by
    rw [iteratedFDeriv_fun_sum_apply
      (fun i _ => ((hf i).contDiffAt (c.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
    calc
      _ ≤ ∑ i : Fin N, ‖iteratedFDeriv ℝ q (f i) z‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hb i)
      _ = (N : ℝ) * B := by simp
  have hadd (f g : V → ℝ) (hf : ContDiffOn ℝ ∞ f c.target)
      (hg : ContDiffOn ℝ ∞ g c.target) (z : V) (hz : z ∈ c.target) (q : ℕ) :
      ‖iteratedFDeriv ℝ q (fun y => f y + g y) z‖ ≤
        ‖iteratedFDeriv ℝ q f z‖ + ‖iteratedFDeriv ℝ q g z‖ := by
    rw [fun_iteratedFDeriv_add_apply
      ((hf.contDiffAt (c.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))
      ((hg.contDiffAt (c.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
    exact norm_add_le _ _
  obtain ⟨⟨BH0, hBH0, hH0⟩, hL0⟩ :=
    ricciFlow_inverse_and_lowered_frame_terminal_bounds hT F hRm ha haT x0 hQ hQbase
  have hH0' (s : ℝ) (hs : s ∈ Ico a T) (z : V) (hz : z ∈ K) (i j : Fin n) :
      ‖iteratedFDeriv ℝ 0 (H s i j) z‖ ≤ BH0 := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hH0 s hs (c.symm z) (mem_image_of_mem _ hz) i j
  have hL0' (r : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ alpha : Fin (r + 4) → Fin n,
        ‖iteratedFDeriv ℝ 0 (L r s alpha) z‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hL0 r
    refine ⟨B, hB, ?_⟩
    intro s hs z hz alpha
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hb s hs (c.symm z) (mem_image_of_mem _ hz) alpha
  have hind : ∀ q ≤ m,
      (∃ B : ℝ, 0 ≤ B ∧
        ∀ p ≤ q, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
          ‖iteratedFDeriv ℝ p (H s i j) z‖ ≤ B) ∧
      (∀ r : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ p ≤ q, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ alpha : Fin (r + 4) → Fin n,
          ‖iteratedFDeriv ℝ p (L r s alpha) z‖ ≤ B) := by
    intro q
    induction q with
    | zero =>
      intro _
      constructor
      · refine ⟨BH0, hBH0, ?_⟩
        intro p hp s hs z hz i j
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact hH0' s hs z hz i j
      · intro r
        obtain ⟨B, hB, hb⟩ := hL0' r
        refine ⟨B, hB, ?_⟩
        intro p hp s hs z hz alpha
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact hb s hs z hz alpha
    | succ q ih =>
      intro hqm
      obtain ⟨⟨BH, hBH, hHbound⟩, hLbound⟩ := ih (Nat.le_succ q |>.trans hqm)
      have hq : q < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hqm
      have hAbound' (s : ℝ) (hs : s ∈ Ico a T) (z : V) (hz : z ∈ K)
          (i j l : Fin n) (p : ℕ) (hp : p ≤ q) :
          ‖iteratedFDeriv ℝ p (Gamma s i j l) z‖ ≤ A :=
        hAbound p (hp.trans_lt hq) s hs z hz i j l
      constructor
      · let P := (2 : ℝ) ^ q * A * BH
        let C1 := (n : ℝ) * (P + P)
        have hP : 0 ≤ P := by dsimp only [P]; positivity
        have hC1 : 0 ≤ C1 := mul_nonneg (Nat.cast_nonneg _) (add_nonneg hP hP)
        refine ⟨max BH ((n : ℝ) * C1), hBH.trans (le_max_left _ _), ?_⟩
        intro p hp s hs z hz j k
        by_cases hpq : p ≤ q
        · exact (hHbound p hpq s hs z hz j k).trans (le_max_left _ _)
        have hpnext : p = q + 1 := by omega
        subst p
        let b := fun (i : Fin n) (y : V) =>
          -(∑ l : Fin n, (Gamma s i l j y * H s l k y +
            Gamma s i l k y * H s j l y))
        have hbSmooth (i : Fin n) : ContDiffOn ℝ ∞ (b i) c.target :=
          (ContDiffOn.sum (fun l _ =>
            ((hGammaSmooth s i l j).mul (hHSmooth s l k)).add
              ((hGammaSmooth s i l k).mul (hHSmooth s j l)))).neg
        have hbBound (i : Fin n) : ‖iteratedFDeriv ℝ q (b i) z‖ ≤ C1 := by
          change ‖iteratedFDeriv ℝ q (-(fun y : V =>
            ∑ l : Fin n, (Gamma s i l j y * H s l k y +
              Gamma s i l k y * H s j l y))) z‖ ≤ C1
          rw [iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := q) (x := z), norm_neg]
          apply hsum _ (fun l =>
            ((hGammaSmooth s i l j).mul (hHSmooth s l k)).add
              ((hGammaSmooth s i l k).mul (hHSmooth s j l))) z (hKchart hz) q (P + P)
          intro l
          apply (hadd _ _ ((hGammaSmooth s i l j).mul (hHSmooth s l k))
            ((hGammaSmooth s i l k).mul (hHSmooth s j l)) z (hKchart hz) q).trans
          apply add_le_add
          · exact norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
              (hGammaSmooth s i l j) (hHSmooth s l k) (hKchart hz) q hA hBH
              (hAbound' s hs z hz i l j) (fun p hp => hHbound p hp s hs z hz l k)
          · exact norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
              (hGammaSmooth s i l k) (hHSmooth s j l) (hKchart hz) q hA hBH
              (hAbound' s hs z hz i l k) (fun p hp => hHbound p hp s hs z hz j l)
        exact (norm_iteratedFDeriv_succ_le_of_coordinate_bounds c.open_target
          (hHSmooth s j k) hbSmooth (fun y hy i => hHderiv s y hy i j k)
          (hKchart hz) q hC1 hbBound).trans (le_max_right _ _)
      · intro r
        obtain ⟨BL, hBL, hBLbound⟩ := hLbound r
        obtain ⟨BN, hBN, hBNbound⟩ := hLbound (r + 1)
        let P := (2 : ℝ) ^ q * A * BL
        let C1 := BN + (r + 4 : ℕ) * ((n : ℝ) * P)
        have hP : 0 ≤ P := by dsimp only [P]; positivity
        have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
        refine ⟨max BL ((n : ℝ) * C1), hBL.trans (le_max_left _ _), ?_⟩
        intro p hp s hs z hz alpha
        by_cases hpq : p ≤ q
        · exact (hBLbound p hpq s hs z hz alpha).trans (le_max_left _ _)
        have hpnext : p = q + 1 := by omega
        subst p
        let d := fun (i : Fin n) (j : Fin (r + 4)) (l : Fin n) (y : V) =>
          Gamma s i (alpha j) l y * L r s (Function.update alpha j l) y
        let b := fun (i : Fin n) (y : V) =>
          L (r + 1) s (Fin.cons i alpha) y + ∑ j : Fin (r + 4), ∑ l : Fin n, d i j l y
        have hdSmooth (i : Fin n) (j : Fin (r + 4)) (l : Fin n) :
            ContDiffOn ℝ ∞ (d i j l) c.target :=
          (hGammaSmooth s i (alpha j) l).mul (hLSmooth r s (Function.update alpha j l))
        have hbSmooth (i : Fin n) : ContDiffOn ℝ ∞ (b i) c.target :=
          (hLSmooth (r + 1) s (Fin.cons i alpha)).add
            (ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun l _ => hdSmooth i j l)))
        have hbBound (i : Fin n) : ‖iteratedFDeriv ℝ q (b i) z‖ ≤ C1 := by
          apply (hadd _ _ (hLSmooth (r + 1) s (Fin.cons i alpha))
            (ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun l _ => hdSmooth i j l)))
            z (hKchart hz) q).trans
          apply add_le_add (hBNbound q le_rfl s hs z hz (Fin.cons i alpha))
          apply hsum _ (fun j => ContDiffOn.sum (fun l _ => hdSmooth i j l))
            z (hKchart hz) q ((n : ℝ) * P)
          intro j
          apply hsum _ (hdSmooth i j) z (hKchart hz) q P
          intro l
          exact norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
            (hGammaSmooth s i (alpha j) l) (hLSmooth r s (Function.update alpha j l))
            (hKchart hz) q hA hBL (hAbound' s hs z hz i (alpha j) l)
            (fun p hp => hBLbound p hp s hs z hz (Function.update alpha j l))
        exact (norm_iteratedFDeriv_succ_le_of_coordinate_bounds c.open_target
          (hLSmooth r s alpha) hbSmooth (fun y hy i => hLderiv r s y hy i alpha)
          (hKchart hz) q hC1 hbBound).trans (le_max_right _ _)
  exact hind m le_rfl

end PoincareConjecture.Proofs.M03
