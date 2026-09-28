import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixArea
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Support
import Mathlib.Logic.Equiv.Fin.Rotate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

set_option maxHeartbeats 800000 in
set_option linter.unusedVariables false in
theorem PoincareConjecture.RiemannianMetric.shifted_tilted_openFiber_derivatives_and_area
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((m+1)+k))) M]
    [IsManifold (𝓡 ((m+1)+k)) ∞ M]
    (g : RiemannianMetric ((m+1)+k) M) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 ((m+1)+k)) x),
      -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ) (F G : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ (h i))
    (hF : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ F)
    (hG : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ G)
    (U : Opens M) {δ H r η s : ℝ} (hδ : 0≤δ)
    (hsmall : δ≤1/(8*((k:ℝ)+2))) (hHnonneg : 0≤H)
    (hr : 0<r) (hr1 : r≤1) (hη : 0<η) (hs : 0<s)
    (hunit : ∀ x∈U, ∀ i : Fin (k+1),
      g.tangentNorm x (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) i) x)≤1 ∧
      g.tangentNorm x (g.gradient ((Fin.cons G h : Fin (k+1) → M → ℝ) i) x)≤1)
    (hpair : ∀ x∈U, ∀ i : Fin (k+1),
      g.inner x (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) i) x)
        (g.gradient ((Fin.cons G h : Fin (k+1) → M → ℝ) i) x)≤ -1+2*δ)
    (hcross : ∀ x∈U, ∀ i j : Fin (k+1), i≠j →
      |g.inner x (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) i) x)
        (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) j) x)|≤δ)
    (htight : ∀ x∈U, ∀ i j : Fin (k+1), i≠j →
      g.inner x (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) i) x)
        (g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) j) x)≤0)
    (hH : ∀ x∈U, ∀ i : Fin (k+1), ∀ v : TangentSpace (𝓡 ((m+1)+k)) x,
      D.hessian ((Fin.cons F f : Fin (k+1) → M → ℝ) i) x v v≤(H/r)*g.inner x v v)
    (p : M) (b : ℝ) :
    let P := fun x i => f i x
    let hP : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x∈U, Surjective (mfderiv (𝓡 ((m+1)+k)) 𝓘(ℝ,Fin k → ℝ) P x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k)))=(m+1)+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m+1) hP U hreg c
        letI := isManifold_openFiber (m := m+1) hP U hreg c
        let gP := g.openRegularFiberMetric hP U hreg c
        let φ := fun z : openFiber P U c => F (openFiberIncl P U c z)-b+s/16
        ∃ hφ : ContMDiff (𝓡 (m+1)) 𝓘(ℝ,ℝ) ∞ φ,
          (∀ z, (1/2≤gP.tangentNorm z (gP.gradient φ z) ∧
            gP.tangentNorm z (gP.gradient φ z)≤1) ∧
            ∀ v : TangentSpace (𝓡 (m+1)) z,
              gP.leviCivitaData.hessian φ z v v≤(2*H/r)*gP.inner z v v) ∧
          ∀ (t : ℝ), 0<t → t<s/8 →
            (∀ (x : M), x∈U → P x=c → F x=t+b-s/16 →
              g.edist p x<ENNReal.ofReal (2*r)) →
            (∀ (x : M), x∈U → P x=c → F x=t+b-s/16 → ∀ (y : M),
              g.edist x y≤ENNReal.ofReal (η*r) → y∈U) →
            gP.regularLevelArea hφ t≤
              RiemannianMetric.annularCornerVolumeConstant m (k+1) H η*r^m := by
  classical
  let φ₀ := fun x => F x-b+s/16
  let fs : Fin (k+1) → M → ℝ := Fin.snoc f φ₀
  let e := finRotate (k+1)
  let w := fun x i => g.gradient ((Fin.cons G h : Fin (k+1) → M → ℝ) (e i)) x
  have hφ₀ : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ φ₀ :=
    (hF.sub contMDiff_const).add contMDiff_const
  have hfs : ∀ i, ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,ℝ) ∞ (fs i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [fs,Fin.snoc_last] using hφ₀
    · simpa only [fs,Fin.snoc_castSucc] using hf j
  have hshift : φ₀=(fun x => (-b+s/16)+F x) := by funext x; dsimp [φ₀]; ring
  have hgrad (i : Fin (k+1)) (x:M) :
      g.gradient (fs i) x = g.gradient ((Fin.cons F f : Fin (k+1) → M → ℝ) (e i)) x := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [fs,Fin.snoc_last,e,finRotate_last,Fin.cons_zero]
      rw [hshift]
      exact D.gradient_const_add_at ((hF x).mdifferentiableAt (by simp)) _
    · have he : e j.castSucc=j.succ := finRotate_of_lt j.isLt
      simp only [fs,Fin.snoc_castSucc,he,Fin.cons_succ]
  have hhess (i : Fin (k+1)) (x:M) (v : TangentSpace (𝓡 ((m+1)+k)) x) :
      D.hessian (fs i) x v v =
        D.hessian ((Fin.cons F f : Fin (k+1) → M → ℝ) (e i)) x v v := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [fs,Fin.snoc_last,e,finRotate_last,Fin.cons_zero]
      rw [hshift]
      exact D.hessian_const_add_at (hF x) _ _ _
    · have he : e j.castSucc=j.succ := finRotate_of_lt j.isLt
      simp only [fs,Fin.snoc_castSucc,he,Fin.cons_succ]
  have hresult := g.strainer_prefix_regularLevelArea_le_annular_mul_pow
    D hc hsec fs w hfs U hδ hsmall hHnonneg
    (fun x hx i => by simpa only [hgrad] using hunit x hx (e i))
    (fun x hx i => by simpa only [hgrad] using hpair x hx (e i))
    (fun x hx i j hij => by simpa only [hgrad] using hcross x hx (e i) (e j) (e.injective.ne hij))
    (fun x hx i j hij => by simpa only [hgrad] using htight x hx (e i) (e j) (e.injective.ne hij))
    (fun x hx i v => by simpa only [hhess] using hH x hx (e i) v)
    p hr hr1 hη
  have hprefix : (fun x (i:Fin k) => fs i.castSucc x)=(fun x i => f i x) := by
    funext x i
    simp only [fs,Fin.snoc_castSucc]
  have hlast : fs (Fin.last k)=φ₀ := by simp only [fs,Fin.snoc_last]
  have hresult' :
      ∃ hP : ContMDiff (𝓡 ((m+1)+k)) 𝓘(ℝ,Fin k → ℝ) ∞
          (fun x (i:Fin k) => fs i.castSucc x),
      ∃ hp : ∀ x∈U, Surjective (mfderiv (𝓡 ((m+1)+k)) 𝓘(ℝ,Fin k → ℝ)
          (fun y (i:Fin k) => fs i.castSucc y) x),
        ∀ c : Fin k → ℝ,
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+1)+k)))=(m+1)+k) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI := openFiberChartedSpace (m := m+1) hP U hp c
          letI := isManifold_openFiber (m := m+1) hP U hp c
          let gP := g.openRegularFiberMetric hP U hp c
          let φ := fs (Fin.last k) ∘ openFiberIncl (fun x (i:Fin k) => fs i.castSucc x) U c
          ∃ hφ : ContMDiff (𝓡 (m+1)) 𝓘(ℝ,ℝ) ∞ φ,
            (∀ z, (1/2≤gP.tangentNorm z (gP.gradient φ z) ∧
              gP.tangentNorm z (gP.gradient φ z)≤1) ∧
              ∀ v : TangentSpace (𝓡 (m+1)) z,
                gP.leviCivitaData.hessian φ z v v≤(2*H/r)*gP.inner z v v) ∧
            ∀ t : ℝ,
              (∀ x∈U, (fun (i:Fin k) => fs i.castSucc x)=c → fs (Fin.last k) x=t →
                g.edist p x<ENNReal.ofReal (2*r)) →
              (∀ x∈U, (fun (i:Fin k) => fs i.castSucc x)=c → fs (Fin.last k) x=t → ∀ y,
                g.edist x y≤ENNReal.ofReal (η*r) → y∈U) →
              gP.regularLevelArea hφ t≤
                RiemannianMetric.annularCornerVolumeConstant m (k+1) H η*r^m := by
    exact ⟨contMDiff_pi_space.mpr (fun i => hfs i.castSucc), hresult⟩
  rw [hprefix,hlast] at hresult'
  obtain ⟨_,hpre,harea⟩ := hresult'
  refine ⟨hpre,?_⟩
  intro c
  obtain ⟨hφ,hbounds,hvol⟩ := harea c
  refine ⟨hφ,hbounds,?_⟩
  intro t ht ht' hinside hbuffer
  apply hvol t
  · intro x hx hfx he
    apply hinside x hx ((congrFun hprefix x).symm.trans hfx)
    change F x-b+s/16=t at he
    linarith
  · intro x hx hfx he
    apply hbuffer x hx ((congrFun hprefix x).symm.trans hfx)
    change F x-b+s/16=t at he
    linarith
