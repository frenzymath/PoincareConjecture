import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.TiltedArea
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.WeightedBound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.IteratedFiber.Components
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.ConnectedComponent.ScalarBound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalErrorBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.AugmentedRegularity








open Set Function TopologicalSpace MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
universe u

theorem PoincareConjecture.RiemannianMetric.exists_shifted_tilted_fiber_scalar_slab_bound
    (m k : ℕ) (hm : 1 ≤ m) {δ ℓ H η C₀ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 2)^2))
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hH : 0 ≤ H) (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    let ρ := min 1 (η / 80)
    let A := 9 * Real.exp (256 * H * ρ)
    let q := ρ / (4 * A ^ (k + 1))
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume ((m + 2) + k) 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume ((m + 2) + k) 1 (q / 2)⌉₊
    let Λ := max 1 ((N : ℝ) * ρ)
    let β := min (40 * ρ) (q / 4)
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 2) + k))) M]
        [IsManifold (𝓡 ((m + 2) + k)) ∞ M],
        PoincareConjecture.NormalizedCornerScalarBound ((m + 2) + k) (m + 1) (k + 1)
          (by omega) M δ (Λ * H) (β / Λ) C₀ →
        ∀ (g : PoincareConjecture.RiemannianMetric ((m + 2) + k) M)
          (D : PoincareConjecture.LeviCivitaData g),
          PoincareConjecture.MetricComplete g →
          (∀ x (v w : TangentSpace (𝓡 ((m + 2) + k)) x),
            -1 ≤ D.sectionalCurvature x v w) →
          ∀ (f h : Fin k → M → ℝ) (F G : M → ℝ)
            (hf : ∀ i, ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
            (_hh : ∀ i, ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ, ℝ) ∞ (h i))
            (hF : ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ, ℝ) ∞ F)
            (_hG : ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ, ℝ) ∞ G)
            (U : Opens M) (p : M) (r b : ℝ),
            0 < r → r ≤ 1 / 2 → Λ * r ≤ 1 →
            let f' := Fin.cons F f
            let h' := Fin.cons G h
            (∀ x ∈ U, ∀ i,
              g.tangentNorm x (D.gradient (f' i) x) ≤ 1 ∧
              g.tangentNorm x (D.gradient (h' i) x) ≤ 1) →
            (∀ x ∈ U, ∀ i,
              g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * δ) →
            (∀ x ∈ U, ∀ i j, i ≠ j →
              |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ δ ∧
              |g.inner x (D.gradient (f' i) x) (D.gradient (h' j) x)| ≤ δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ δ ∧
              |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ δ) →
            (∀ x ∈ U, ∀ i j, i ≠ j →
              g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) →
            (∀ x ∈ U, ∀ i v,
              D.hessian (f' i) x v v ≤ (H / r) * g.inner x v v ∧
              D.hessian (h' i) x v v ≤ (H / r) * g.inner x v v) →
            let P := fun x i => f i x
            let hP : ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
              contMDiff_pi_space.mpr hf
            ∃ hreg : ∀ x ∈ U, Surjective
                (mfderiv (𝓡 ((m + 2) + k)) 𝓘(ℝ, Fin k → ℝ) P x),
              ∀ c : Fin k → ℝ,
                letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m + 2) + k))) =
                  (m + 2) + k) := ⟨finrank_euclideanSpace_fin⟩
                letI := openFiberChartedSpace (m := m + 2) hP U hreg c
                letI := isManifold_openFiber (m := m + 2) hP U hreg c
                let gP := g.openRegularFiberMetric hP U hreg c
                let DP := gP.leviCivitaData
                let Fp := F ∘ openFiberIncl P U c
                let φ := fun x : openFiber P U c => Fp x - b + ℓ * r / 16
                let hφ : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ :=
                  ((hF.comp (contMDiff_openFiberIncl (m := m + 2) hP U hreg c)).sub
                    contMDiff_const).add contMDiff_const
                let J := Ioo (b - ℓ * r / 16) (b + ℓ * r / 16)
                IsProperMap (J.restrictPreimage Fp) →
                (∀ x ∈ U, P x = c → F x ∈ J →
                  g.edist p x < ENNReal.ofReal (2 * r)) →
                (∀ x ∈ U, P x = c → F x ∈ J → ∀ y : M,
                  g.edist x y ≤ ENNReal.ofReal (η * r) → y ∈ U) →
                ∀ K : openFiber P U c → ℝ,
                  ContinuousOn K (gP.regularDomain hφ) →
                  (∀ x ∈ φ ⁻¹' Icc (3 * (ℓ * r) / 64) (15 * (ℓ * r) / 128),
                    0 ≤ K x) →
                  (∀ x ∈ φ ⁻¹' Icc (3 * (ℓ * r) / 64) (15 * (ℓ * r) / 128),
                    ∀ v w : TangentSpace (𝓡 (m + 2)) x,
                      -K x ≤ DP.sectionalCurvature x v w) →
                  (∫ x in φ ⁻¹' Icc (3 * (ℓ * r) / 64) (5 * (ℓ * r) / 64),
                    max 0 (DP.scalarCurvature x) ∂gP.volumeMeasure) ≤
                    B * (r ^ m + ∫ x in φ ⁻¹' Icc (3 * (ℓ * r) / 64)
                      (15 * (ℓ * r) / 128), K x ∂gP.volumeMeasure) := by
  classical
  let ρ := min 1 (η / 80)
  let A := 9 * Real.exp (256 * H * ρ)
  let q := ρ / (4 * A ^ (k + 1))
  let N := ⌈RiemannianMetric.modelVolume ((m + 2) + k) 1 3 /
    RiemannianMetric.modelVolume ((m + 2) + k) 1 (q / 2)⌉₊
  let Λ := max 1 ((N : ℝ) * ρ)
  let β := min (40 * ρ) (q / 4)
  let V := RiemannianMetric.annularCornerVolumeConstant (m+1) (k+1) H η
  have hV : 0 ≤ V := (RiemannianMetric.annularCornerVolumeConstant_pos
    (m+1) (k+1) H hη).le
  have hΛ : 0 ≤ Λ := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨α, B, hα, hB, hcoef, hmain⟩ :=
    LeviCivitaData.exists_uniform_weighted_component_slab_bound_with_coefficient.{u}
      m hm hℓ hℓ1 hV (mul_nonneg (by norm_num : (0:ℝ)≤2) hH) hC₀ hΛ N
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ _ _ hIH g D hc hsec f h F G hf hh hF hG U p r b hr hrhalf hscale
    f' h' hunit hpair hcross htight hhess
  let P := fun x i => f i x
  have hP : ContMDiff (𝓡 ((m+2)+k)) 𝓘(ℝ,Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr hf
  have hsmallArea : δ ≤ 1/(8*((k:ℝ)+2)) := by
    refine hsmall.trans ?_
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith only [show 0 ≤ (k:ℝ) by positivity]
  obtain ⟨hreg, harea⟩ := g.shifted_tilted_openFiber_derivatives_and_area
    (m := m+1) D hc hsec f h F G hf hh hF hG U hδ hsmallArea hH hr
    (by linarith only [hrhalf]) hη (mul_pos hℓ hr) hunit hpair
    (fun x hx i j hij => (hcross x hx i j hij).1) htight
    (fun x hx i v => (hhess x hx i v).1) p b
  let fs : Fin (k+1) → M → ℝ := fun i x =>
    Fin.cons (α := fun _ : Fin (k+1) => ℝ) (F x) (P x) i
  let hs : Fin (k+1) → M → ℝ := fun i x =>
    Fin.cons (α := fun _ : Fin (k+1) => ℝ) (G x) (fun j => h j x) i
  have hfsEq : fs = f' := by
    funext i x
    exact Fin.cases rfl (fun _ => rfl) i
  have hhsEq : hs = h' := by
    funext i x
    exact Fin.cases rfl (fun _ => rfl) i
  have hfs : ∀ i, ContMDiff (𝓡 ((m+2)+k)) 𝓘(ℝ,ℝ) ∞ (fs i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hF
    · exact hf j
  have hhs : ∀ i, ContMDiff (𝓡 ((m+2)+k)) 𝓘(ℝ,ℝ) ∞ (hs i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hG
    · exact hh j
  obtain ⟨hfull, hcomponents⟩ :=
    RiemannianMetric.strainer_openFiber_component_scalar_bound_of_dimension
      (m := m+1) (k := k+1) (by omega) (by omega) hδ
      (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1:ℝ)+1=2 by norm_num] using hsmall)
      hH hη hC₀ hIH g D hc hsec fs hs hfs hhs U p hr hrhalf hscale
      (by simpa only [hfsEq,hhsEq] using hunit)
      (by simpa only [hfsEq,hhsEq] using hpair)
      (by simpa only [hfsEq,hhsEq] using hcross)
      (by simpa only [hfsEq,hhsEq] using htight)
      (by simpa only [hfsEq,hhsEq] using hhess)
  let joint := fun x => Fin.cons (α := fun _ : Fin (k+1) => ℝ) (F x) (P x)
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k)))=(m+2)+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI (c : Fin k → ℝ) := openFiberChartedSpace (m := m+2) hP U hreg c
  letI (c : Fin k → ℝ) := isManifold_openFiber (m := m+2) hP U hreg c
  have hFreg (c : Fin k → ℝ) (x : openFiber P U c) :
      mfderiv (𝓡 (m+2)) 𝓘(ℝ,ℝ) (F ∘ openFiberIncl P U c) x ≠ 0 :=
    regular_openFiber_restriction_of_surjective_mfderiv_cons hP hF U hreg c x
      (hfull (openFiberIncl P U c x) x.1.2)
  obtain ⟨hjoint, hjsmooth, hbridge⟩ :=
    g.exists_shifted_iterated_openFiber_component_equivalence
      (m := m+1) hP hF U hreg hFreg
  refine ⟨hreg, ?_⟩
  intro c
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k)))=(m+2)+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openFiberChartedSpace (m := m+2) hP U hreg c
  letI := isManifold_openFiber (m := m+2) hP U hreg c
  let gP := g.openRegularFiberMetric hP U hreg c
  let DP := gP.leviCivitaData
  let Fp := F ∘ openFiberIncl P U c
  let φ := fun x : openFiber P U c => Fp x-b+ℓ*r/16
  let hφ : ContMDiff (𝓡 (m+2)) 𝓘(ℝ,ℝ) ∞ φ :=
    ((hF.comp (contMDiff_openFiberIncl (m := m+2) hP U hreg c)).sub
      contMDiff_const).add contMDiff_const
  let J := Ioo (b-ℓ*r/16) (b+ℓ*r/16)
  change IsProperMap (J.restrictPreimage Fp) → _
  intro hproper hinside hbuffer K hKc hK hKsec
  obtain ⟨_, hderiv, hlevelarea⟩ := harea c
  have hφreg (x : openFiber P U c) :
      mfderiv (𝓡 (m+2)) 𝓘(ℝ,ℝ) φ x ≠ 0 := by
    intro hz
    have hg : gP.gradient φ x = 0 := (RiemannianMetric.gradient_eq_zero_iff_mfderiv_eq_zero gP φ x).mpr hz
    have hs := (hderiv x).1.1
    change 1/2 ≤ gP.tangentNorm x (gP.gradient φ x) at hs
    simp only [hg, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hs
    norm_num at hs
  have htband (t : ℝ) (ht : t ∈ Icc (3*(ℓ*r)/64) (15*(ℓ*r)/128)) :
      0<t ∧ t<ℓ*r/8 := by
    constructor <;> nlinarith only [ht.1,ht.2,mul_pos hℓ hr]
  have hFJ (t : ℝ) (ht : 0<t ∧ t<ℓ*r/8) :
      t+b-ℓ*r/16 ∈ J := by
    change b-ℓ*r/16<t+b-ℓ*r/16 ∧ t+b-ℓ*r/16<b+ℓ*r/16
    constructor <;> linarith only [ht.1,ht.2]
  have htop : 3*(5*(ℓ*r)/64)/2 = 15*(ℓ*r)/128 := by ring
  have hproperφ : IsProperMap ((Ioo (0:ℝ) (ℓ*r/8)).restrictPreimage φ) :=
    hproper.restrictPreimage_shifted_interval
  have hareaφ (t : ℝ) (ht : t ∈ Icc (3*(ℓ*r)/64) (15*(ℓ*r)/128)) :
      gP.regularLevelArea hφ t ≤ V*r^(m+1) :=
    hlevelarea t (htband t ht).1 (htband t ht).2
      (fun x hx hxP hxF => hinside x hx hxP (hxF.symm ▸ hFJ t (htband t ht)))
      (fun x hx hxP hxF => hbuffer x hx hxP (hxF.symm ▸ hFJ t (htband t ht)))
  let W := gP.regularDomain hφ
  let hφW := gP.regularDomain_regular hφ
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+2)))=m+2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI (t : ℝ) := openLevelSetChartedSpace hφ W hφW (m+1) t
  letI (t : ℝ) := isManifold_openLevelSet hφ W hφW (m+1) t
  have hgeometry (t : ℝ) (ht : t ∈ Icc (3*(ℓ*r)/64) (15*(ℓ*r)/128)) :
      Nat.card (ConnectedComponents (openLevelSet φ W t)) ≤ N ∧
      ∀ z : openLevelSet φ W t,
        let gL := RiemannianMetric.regularLevelMetric hφ W hφW t gP
        (∫ x, max 0 ((gL.connectedComponentMetric z).leviCivitaData.scalarCurvature x)
          ∂(gL.connectedComponentMetric z).volumeMeasure) ≤
        C₀*((Λ*r)^(m-1)+∫ x, DP.levelSectionalError φ K (α/t)
          (openLevelIncl φ W t x) ∂(gL.connectedComponentMetric z).volumeMeasure) := by
    have hshift : (fun x : openFiber P U c =>
        F (openFiberIncl P U c x)-(b-ℓ*r/16))=φ := by
      funext x
      dsimp [φ,Fp]
      ring
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k)))=
        (m+1)+(k+1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
    letI := openFiberChartedSpace (m := m+1) hjsmooth U hjoint
      (Fin.cons (t+(b-ℓ*r/16)) c)
    letI := isManifold_openFiber (m := m+1) hjsmooth U hjoint
      (Fin.cons (t+(b-ℓ*r/16)) c)
    let gJ : RiemannianMetric (m+1) (openFiber joint U (Fin.cons (t+(b-ℓ*r/16)) c)) :=
      RiemannianMetric.Induced.pullbackMetric g
        (openFiberIncl joint U (Fin.cons (t+(b-ℓ*r/16)) c))
        (contMDiff_openFiberIncl (m := m+1) hjsmooth U hjoint _)
        (injective_mfderiv_openFiberIncl (m := m+1) hjsmooth U hjoint _)
    let ψ := fun x : openFiber P U c => F (openFiberIncl P U c x)-(b-ℓ*r/16)
    have hψ : ContMDiff (𝓡 (m+2)) 𝓘(ℝ,ℝ) ∞ ψ :=
      (hF.comp (contMDiff_openFiberIncl (m := m+2) hP U hreg c)).sub contMDiff_const
    let Wψ := gP.regularDomain hψ
    let hψW := gP.regularDomain_regular hψ
    letI := openLevelSetChartedSpace hψ Wψ hψW (m+1) t
    letI := isManifold_openLevelSet hψ Wψ hψW (m+1) t
    obtain ⟨e₁, he₁, hm₁, hcomp₁⟩ := hbridge c (b-ℓ*r/16) t
    have hsame (x : openFiber P U c) :
        (x∈W ∧ φ x=t) ↔ (x∈Wψ ∧ ψ x=t) := by
      have hx : x∈W := (gP.mem_regularDomain_iff hφ x).mpr (hφreg x)
      have hxψ : x∈Wψ := (gP.mem_regularDomain_iff hψ x).mpr (by
        change mfderiv (𝓡 (m+2)) 𝓘(ℝ,ℝ) ψ x ≠ 0
        rw [show ψ=φ from hshift]
        exact hφreg x)
      simp only [hx,hxψ,true_and,show ψ x=φ x from congrFun hshift x]
    let e₀ := openLevelDiffeomorphOfEq hφ hψ (m+1) hφW hψW hsame
    let e := e₀.trans e₁
    let gL := RiemannianMetric.regularLevelMetric hφ W hφW t gP
    let gS := RiemannianMetric.regularLevelMetric hψ Wψ hψW t gP
    have hm₀ (x : openLevelSet φ W t) (v w : TangentSpace (𝓡 (m+1)) x) :
        gL.inner x v w=gS.inner (e₀ x)
          (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x v)
          (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x w) :=
      gP.regularLevelMetric_inner_equivOfEq hφ hψ hφW hψW hsame x v w
    have hmE (x : openLevelSet φ W t) (v w : TangentSpace (𝓡 (m+1)) x) :
        gL.inner x v w=gJ.inner (e x)
          (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e x v)
          (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e x w) := by
      have hd := mfderiv_comp x (e₁.contMDiff.mdifferentiable (by simp) (e₀ x))
        (e₀.contMDiff.mdifferentiable (by simp) x)
      change mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e x = _ at hd
      calc
        _ = gS.inner (e₀ x)
            (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x v)
            (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x w) := hm₀ x v w
        _ = gJ.inner (e x)
            (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₁ (e₀ x)
              (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x v))
            (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₁ (e₀ x)
              (mfderiv (𝓡 (m+1)) (𝓡 (m+1)) e₀ x w)) :=
          hm₁ (e₀ x) _ _
        _ = _ := congrArg₂ (fun v w => gJ.inner (e x) v w)
          (congrArg (fun L => L v) hd).symm (congrArg (fun L => L w) hd).symm
    have hi (x : M) (hx : x∈U) (hval : joint x=Fin.cons (t+(b-ℓ*r/16)) c) :
        x∈g.ball p (2*r) := by
      apply hinside x hx
      · funext i
        exact congrFun hval i.succ
      · have hv : F x=t+b-ℓ*r/16 := by
          have hv := congrFun hval 0
          change F x=t+(b-ℓ*r/16) at hv
          linarith only [hv]
        exact hv.symm ▸ hFJ t (htband t ht)
    have hbuf (x : M) (hx : x∈U) (hval : joint x=Fin.cons (t+(b-ℓ*r/16)) c) :
        ∀ y : M, g.edist x y≤ENNReal.ofReal (η*r) → y∈U := by
      apply hbuffer x hx
      · funext i
        exact congrFun hval i.succ
      · have hv : F x=t+b-ℓ*r/16 := by
          have hv := congrFun hval 0
          change F x=t+(b-ℓ*r/16) at hv
          linarith
        exact hv.symm ▸ hFJ t (htband t ht)
    have hgeom := hcomponents (Fin.cons (t+(b-ℓ*r/16)) c) hi hbuf
    letI := hgeom.2.2.1
    have hsurj := e.symm.contMDiff.continuous.connectedComponentsMap_surjective e.symm.surjective
    have hcard := Nat.card_le_card_of_surjective _ hsurj
    refine ⟨hcard.trans hgeom.2.2.2.1, ?_⟩
    intro z
    let gL := RiemannianMetric.regularLevelMetric hφ W hφW t gP
    have hnormH (x : openFiber P U c) (hfx : φ x=t)
        (v : TangentSpace (𝓡 (m+2)) x) :
        DP.hessian φ x v v / Real.sqrt (DP.levelQ φ x) ≤
          (α/t)*gP.inner x v v := by
      have hs : 1/2 ≤ Real.sqrt (DP.levelQ φ x) := (hderiv x).1.1
      have hspos : 0<Real.sqrt (DP.levelQ φ x) := lt_of_lt_of_le (by norm_num) hs
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 (m+2)) :
          openFiber P U c → Type _) := ⟨gP.toRiemannianMetric⟩
      have hinner : 0≤gP.inner x v v := by
        change 0 ≤ inner ℝ v v
        exact real_inner_self_nonneg
      have hbnd : (2*H/r)*gP.inner x v v ≤
          ((2*(2*H)/r)*gP.inner x v v)*Real.sqrt (DP.levelQ φ x) := by
        have hh := mul_le_mul_of_nonneg_left hs
          (by positivity : 0≤(2*(2*H)/r)*gP.inner x v v)
        calc
          _ = (2*(2*H)/r*gP.inner x v v)*(1/2) := by ring
          _ ≤ _ := hh
      calc
        _ ≤ ((2*H/r)*gP.inner x v v)/Real.sqrt (DP.levelQ φ x) :=
          div_le_div_of_nonneg_right ((hderiv x).2 v) hspos.le
        _ ≤ (2*(2*H)/r)*gP.inner x v v := (div_le_iff₀ hspos).mpr hbnd
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef r hr t ht) hinner
    have herror := DP.regularLevel_sectionalError_bounds hφ t hKc
      (fun x hx => hK x (by change φ x ∈ Icc (3*(ℓ*r)/64) (15*(ℓ*r)/128); simpa only [hx] using ht))
      (fun x hx => hKsec x (by change φ x ∈ Icc (3*(ℓ*r)/64) (15*(ℓ*r)/128); simpa only [hx] using ht))
      (div_nonneg hα.le (htband t ht).1.le)
      (fun x hx v _ => hnormH x hx v)
    exact RiemannianMetric.component_scalar_bound_of_diffeomorph gL gJ e hmE
      (DP.levelSectionalError φ K (α/t) ∘ openLevelIncl φ W t)
      herror.1 (fun x => (herror.2 x).1) (fun x => (herror.2 x).2)
      (by simpa only [show m+1-2=m-1 by omega] using hgeom.2.2.2.2.2) z
  have hbound := hmain (openFiber P U c) gP DP φ hφ r hr hproperφ
    (fun x _ => hφreg x) K hKc
    (by simpa only [htop] using hK)
    (by simpa only [htop] using hKsec)
    (by simpa only [htop] using hareaφ)
    (fun x _ v => (hderiv x).2 v) (fun x _ => (hderiv x).1)
    (by simpa only [htop] using (fun t ht => (hgeometry t ht).1))
    (by simpa only [htop] using (fun t ht => (hgeometry t ht).2))
  simpa only [htop] using hbound
