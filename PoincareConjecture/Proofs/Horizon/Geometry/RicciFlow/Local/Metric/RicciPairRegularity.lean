import PoincareConjecture.Proofs.M03.RicciPairRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Metric.MetricPairRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Metric.MetricInverse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Metric.MetricDifferenceEvolution

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contDiffOn_ricciFlow_ricci_chart_pair
    {J : Set ℝ} (F : RicciFlow n M J)
    {U : Set M} (hU : IsOpen U)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (x₀ : M) :
    let c := extChartAt (𝓡 n) x₀
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (F.connection p.1).ricci (c.symm p.2)
          (Y (c.symm p.2)) (Z (c.symm p.2)))
      (interior J ×ˢ (c.target ∩ c.symm ⁻¹' U)) := by
  dsimp only
  let c := extChartAt (𝓡 n) x₀
  let H : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p =>
    (F.metric p.1).inner (c.symm p.2) (Y (c.symm p.2)) (Z (c.symm p.2))
  let R : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p =>
    (F.connection p.1).ricci (c.symm p.2)
      (Y (c.symm p.2)) (Z (c.symm p.2))
  change ContDiffOn ℝ ∞ R (interior J ×ˢ (c.target ∩ c.symm ⁻¹' U))
  have hpair := contMDiffOn_family_metric_pair F.smooth Y Z hY hZ
  have hpair' := hpair.mono
    (show interior J ×ˢ U ⊆ J ×ˢ U from fun _ hp =>
      ⟨interior_subset hp.1, hp.2⟩)
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x₀).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hH (s : ℝ) (hs : s ∈ interior J)
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (hzU : c.symm z ∈ U) : ContDiffAt ℝ ∞ H (s, z) := by
    have hp := (hpair' (s, c.symm z) ⟨hs, hzU⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨hs, hzU⟩)
    have hh := hp.comp (s, z)
      (contMDiffAt_fst.prodMk ((hc z hz).comp (s, z) contMDiffAt_snd))
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffAt
  intro p hp
  rcases p with ⟨s, z⟩
  rcases hp with ⟨hs, hz⟩
  rcases hz with ⟨hzTarget, hzU⟩
  have hHp := hH s hs z hzTarget hzU
  have hFD : ContDiffAt ℝ ∞ (fun q => fderiv ℝ H q (1, 0)) (s, z) := by
    have hCLM := hHp.fderiv_right (m := ∞) (by simp)
    exact hCLM.clm_apply contDiffAt_const
  have hK : ContDiffAt ℝ ∞
      (fun q => (-1 / 2 : ℝ) * fderiv ℝ H q (1, 0)) (s, z) := by
    exact (contDiffAt_const (c := (-1 / 2 : ℝ))).mul hFD
  have htimeSlice (w : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
      HasDerivAt (fun a : ℝ => (a, w)) (1, 0) r := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) r).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) w r)).hasDerivAt
  have hEq : R =ᶠ[𝓝 (s, z)]
      (fun q => (-1 / 2 : ℝ) * fderiv ℝ H q (1, 0)) := by
    have hnJ : interior J ∈ 𝓝 s := isOpen_interior.mem_nhds hs
    have hnTarget : c.target ∈ 𝓝 z := extChartAt_target_mem_nhds' hzTarget
    have hnU : c.symm ⁻¹' U ∈ 𝓝 z :=
      (hc z hzTarget).continuousAt.preimage_mem_nhds (hU.mem_nhds hzU)
    have hn := prod_mem_nhds hnJ (Filter.inter_mem hnTarget hnU)
    filter_upwards [hn] with q hq
    rcases hq with ⟨hqJ, hqTarget, hqU⟩
    have hqH := (hH q.1 hqJ q.2 hqTarget hqU).differentiableAt (by simp)
    have hd := hqH.hasFDerivAt.comp_hasDerivAt q.1 (htimeSlice q.2 q.1)
    have he := (F.equation q.1 (interior_subset hqJ) (c.symm q.2)
      (Y (c.symm q.2)) (Z (c.symm q.2))).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hqJ)
    have hu := hd.unique he
    dsimp [R, H]
    rw [hu]
    ring
  exact (hK.congr_of_eventuallyEq hEq).contDiffWithinAt

section NativeCoordinates

open Bundle Manifold
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

theorem connection_frame_coordinates_eq_inverse_koszul
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let G := fun (i j : Fin n) (z : V) =>
      g.inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    let A := fun z : V => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 (c.symm z) x0 (c.symm z) (g.inner (c.symm z))
    let H := fun (i j : Fin n) (z : V) =>
      (A z).inverse (EuclideanSpace.proj j) i
    let Gamma := fun (i j l : Fin n) (z : V) =>
      theta l (c.symm z) (D.connection (E j) (c.symm z) (E i (c.symm z)))
    let br := fun (i j l : Fin n) (z : V) =>
      theta l (c.symm z) (VectorField.mlieBracket (𝓡 n) (E i) (E j) (c.symm z))
    let K := fun (i j l : Fin n) (z : V) =>
      fderiv ℝ (G j l) z (EuclideanSpace.single i 1) +
      fderiv ℝ (G l i) z (EuclideanSpace.single j 1) -
      fderiv ℝ (G i j) z (EuclideanSpace.single l 1) +
      (∑ p : Fin n, br i j p z * G p l z) -
      (∑ p : Fin n, br i l p z * G j p z) -
      (∑ p : Fin n, br j l p z * G i p z)
    ∀ z ∈ c.target, ∀ i j l : Fin n,
      Gamma i j l z = (1 / 2 : ℝ) * ∑ p : Fin n, H l p z * K i j p z := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := fun (i j : Fin n) (z : V) =>
    g.inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
  let A := fun z : V => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 (c.symm z) x0 (c.symm z) (g.inner (c.symm z))
  let H := fun (i j : Fin n) (z : V) => (A z).inverse (EuclideanSpace.proj j) i
  let Gamma := fun (i j l : Fin n) (z : V) =>
    theta l (c.symm z) (D.connection (E j) (c.symm z) (E i (c.symm z)))
  let br := fun (i j l : Fin n) (z : V) =>
    theta l (c.symm z) (VectorField.mlieBracket (𝓡 n) (E i) (E j) (c.symm z))
  let K := fun (i j l : Fin n) (z : V) =>
    fderiv ℝ (G j l) z (EuclideanSpace.single i 1) +
    fderiv ℝ (G l i) z (EuclideanSpace.single j 1) -
    fderiv ℝ (G i j) z (EuclideanSpace.single l 1) +
    (∑ p : Fin n, br i j p z * G p l z) -
    (∑ p : Fin n, br i l p z * G j p z) -
    (∑ p : Fin n, br j l p z * G i p z)
  change ∀ z ∈ c.target, ∀ i j l : Fin n,
    Gamma i j l z = (1 / 2 : ℝ) * ∑ p : Fin n, H l p z * K i j p z
  intro z hz i j l
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hE (p : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E p)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb p
  have hmd (p : Fin n) : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) (T% (E p)) x :=
    ((hE p).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdir (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) (p : Fin n) :
      mvfderiv (𝓡 n) f x (E p x) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single p 1) := by
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E p x = e.symmL ℝ x (EuclideanSpace.single p 1) := by
      calc
        E p x = e.basisAt cb hx p := e.localFrame_apply_of_mem_baseSet cb hx
        _ = e.symm x (EuclideanSpace.single p 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single p 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single p 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single p 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single p 1) = _
      have hfm := (hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
      erw [mvfderiv_comp_apply z hfm hcs (EuclideanSpace.single p 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hframe (W : TangentSpace (𝓡 n) x) :
      W = ∑ p : Fin n, theta p x W • E p x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V W) hx
  have hbrLeft (a b d : Fin n) :
      g.inner x (VectorField.mlieBracket (𝓡 n) (E a) (E b) x) (E d x) =
        ∑ p : Fin n, br a b p z * G p d z := by
    rw [hframe (VectorField.mlieBracket (𝓡 n) (E a) (E b) x)]
    simp only [br, G, x, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have hbrRight (a b d : Fin n) :
      g.inner x (E d x) (VectorField.mlieBracket (𝓡 n) (E a) (E b) x) =
        ∑ p : Fin n, br a b p z * G d p z := by
    rw [hframe (VectorField.mlieBracket (𝓡 n) (E a) (E b) x)]
    simp only [br, G, x, map_sum, map_smul, smul_eq_mul]
  have hkoszul (p : Fin n) :
      2 * g.inner x (D.connection (E j) x (E i x)) (E p x) = K i j p z := by
    have hpair (a b : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => g.inner y (E a y) (E b y)) e.baseSet :=
      (hE a).inner_bundle (hE b)
    have hk := D.koszul (E i) (E j) (E p) (hmd i) (hmd j) (hmd p)
    rw [hdir _ (hpair j p) i,
      hdir _ (hpair p i) j,
      hdir _ (hpair i j) p,
      hbrLeft i j p, hbrRight i p j, hbrRight j p i] at hk
    exact hk
  let b := g.orthonormalBasis x
  have hGram (p q : Fin n) :
      H p q z = ∑ r, theta p x (b r) * theta q x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx p q
  have hinner (W : TangentSpace (𝓡 n) x) (r) :
      (∑ q : Fin n, theta q x (b r) * g.inner x W (E q x)) = g.inner x W (b r) := by
    nth_rw 2 [hframe (b r)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have horth (W : TangentSpace (𝓡 n) x) :
      (∑ r, g.inner x W (b r) • b r) = W := by
    have hh := b.sum_repr' W
    change (∑ r, g.inner x (b r) W • b r) = W at hh
    simpa only [g.symm x W] using hh
  have hcoeff (p : Fin n) (W : TangentSpace (𝓡 n) x) :
      (∑ q : Fin n, H p q z * g.inner x W (E q x)) = theta p x W := by
    simp only [hGram, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ r, theta p x (b r) *
          (∑ q : Fin n, theta q x (b r) * g.inner x W (E q x)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ r, theta p x (b r) * g.inner x W (b r) := by simp only [hinner]
      _ = theta p x (∑ r, g.inner x W (b r) • b r) := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = _ := by rw [horth]
  calc
    Gamma i j l z = ∑ p : Fin n,
        H l p z * g.inner x (D.connection (E j) x (E i x)) (E p x) :=
      (hcoeff l (D.connection (E j) x (E i x))).symm
    _ = (1 / 2 : ℝ) * ∑ p : Fin n, H l p z * K i j p z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      have hp : g.inner x (D.connection (E j) x (E i x)) (E p x) =
          (1 / 2 : ℝ) * K i j p z := by linarith only [hkoszul p]
      rw [hp]
      ring

theorem curvature_and_ricci_frame_coordinates_eq_connection_coefficients
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let Gamma := fun (i j l : Fin n) (z : V) =>
      theta l (c.symm z) (D.connection (E j) (c.symm z) (E i (c.symm z)))
    let br := fun (i j l : Fin n) (z : V) =>
      theta l (c.symm z) (VectorField.mlieBracket (𝓡 n) (E i) (E j) (c.symm z))
    let R := fun (i j k l : Fin n) (z : V) =>
      fderiv ℝ (Gamma j k l) z (EuclideanSpace.single i 1) -
      fderiv ℝ (Gamma i k l) z (EuclideanSpace.single j 1) +
      (∑ p : Fin n, Gamma j k p z * Gamma i p l z) -
      (∑ p : Fin n, Gamma i k p z * Gamma j p l z) -
      (∑ p : Fin n, br i j p z * Gamma p k l z)
    ∀ z ∈ c.target,
      (∀ i j k l : Fin n,
        theta l (c.symm z) (D.curvature (c.symm z)
          (E i (c.symm z)) (E j (c.symm z)) (E k (c.symm z))) = R i j k l z) ∧
      (∀ i j : Fin n,
        D.ricci (c.symm z) (E i (c.symm z)) (E j (c.symm z)) =
          ∑ p : Fin n, R p i j p z) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let N := fun (i j : Fin n) (y : M) => D.connection (E j) y (E i y)
  let Gamma := fun (i j l : Fin n) (z : V) => theta l (c.symm z) (N i j (c.symm z))
  let br := fun (i j l : Fin n) (z : V) =>
    theta l (c.symm z) (VectorField.mlieBracket (𝓡 n) (E i) (E j) (c.symm z))
  let R := fun (i j k l : Fin n) (z : V) =>
    fderiv ℝ (Gamma j k l) z (EuclideanSpace.single i 1) -
    fderiv ℝ (Gamma i k l) z (EuclideanSpace.single j 1) +
    (∑ p : Fin n, Gamma j k p z * Gamma i p l z) -
    (∑ p : Fin n, Gamma i k p z * Gamma j p l z) -
    (∑ p : Fin n, br i j p z * Gamma p k l z)
  change ∀ z ∈ c.target,
    (∀ i j k l : Fin n,
      theta l (c.symm z) (D.curvature (c.symm z)
        (E i (c.symm z)) (E j (c.symm z)) (E k (c.symm z))) = R i j k l z) ∧
    (∀ i j : Fin n,
      D.ricci (c.symm z) (E i (c.symm z)) (E j (c.symm z)) = ∑ p : Fin n, R p i j p z)
  intro z hz
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hN (i j : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (N i j)) e.baseSet :=
    D.contMDiffOn_connection_apply e.open_baseSet (E i) (E j) (hE i) (hE j)
  have hcoeffSmooth (i j l : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => theta l y (N i j y)) e.baseSet :=
    contMDiffOn_localFrameCoeff cb e.open_baseSet subset_rfl (hN i j) l
  have hdir (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) (i : Fin n) :
      mvfderiv (𝓡 n) f x (E i x) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
      calc
        E i x = e.basisAt cb hx i := e.localFrame_apply_of_mem_baseSet cb hx
        _ = e.symm x (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
      have hfm := (hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
      erw [mvfderiv_comp_apply z hfm hcs (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hcoordDeriv (i j k l : Fin n) :
      theta l x (D.connection (N j k) x (E i x)) =
        fderiv ℝ (Gamma j k l) z (EuclideanSpace.single i 1) +
          ∑ p : Fin n, Gamma j k p z * Gamma i p l z := by
    have hh := localFrame_covariant_derivative_coordinate D x0 (N j k) (hN j k) hx i l
    rw [hdir _ (hcoeffSmooth j k l) i] at hh
    simpa only [Gamma, N, mul_comm] using hh
  have hbrConn (i j k l : Fin n) :
      theta l x (D.connection (E k) x
        (VectorField.mlieBracket (𝓡 n) (E i) (E j) x)) =
          ∑ p : Fin n, br i j p z * Gamma p k l z := by
    have hframe : VectorField.mlieBracket (𝓡 n) (E i) (E j) x =
        ∑ p : Fin n, theta p x
          (VectorField.mlieBracket (𝓡 n) (E i) (E j) x) • E p x :=
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := VectorField.mlieBracket (𝓡 n) (E i) (E j)) hx
    rw [hframe]
    simp only [br, Gamma, N, x, map_sum, map_smul, smul_eq_mul]
  have hcurv (i j k l : Fin n) :
      theta l x (D.curvature x (E i x) (E j x) (E k x)) = R i j k l z := by
    rw [curvature_eq_curvatureOnFields D e.open_baseSet
      (E i) (E j) (E k) (hE i) (hE j) (hE k) hx]
    change theta l x (D.connection (N j k) x (E i x) -
      D.connection (N i k) x (E j x) -
      D.connection (E k) x (VectorField.mlieBracket (𝓡 n) (E i) (E j) x)) = _
    rw [map_sub, map_sub, hcoordDeriv i j k l, hcoordDeriv j i k l, hbrConn i j k l]
    dsimp only [R]
    ring
  refine ⟨hcurv, ?_⟩
  intro i j
  have hcoord (p : Fin n) (W : TangentSpace (𝓡 n) x) :
      theta p x W = (e.basisAt cb hx).repr W p := by
    simpa only [FiberBundle.extend_apply_self] using
      e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) cb hx
        (FiberBundle.extend V W) p
  calc
    D.ricci x (E i x) (E j x) =
        ∑ p : Fin n, theta p x (D.curvature x (E p x) (E i x) (E j x)) := by
      rw [ricci_eq_sum_basis_of_curvature_pairing D x (E i x) (E j x) (e.basisAt cb hx)]
      apply Finset.sum_congr rfl
      intro p _
      rw [hcoord]
      congr 2
      exact congrArg (fun W : TangentSpace (𝓡 n) x =>
        D.curvature x W (E i x) (E j x)) (e.localFrame_apply_of_mem_baseSet cb hx).symm
    _ = ∑ p : Fin n, R p i j p z := Finset.sum_congr rfl (fun p _ => hcurv p i j p)

end NativeCoordinates

section NativeFiniteRegularity

open Bundle Manifold
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

theorem contDiffOn_ricci_coordinate_jets_of_metric_coordinate_jets
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : ℝ → RiemannianMetric n M)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {J : Set ℝ} (hJ : IsOpen J) (x0 : M) (k : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (t : ℝ) (i j : Fin n) (z : V) =>
      (g t).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    let R := fun (t : ℝ) (i j : Fin n) (z : V) =>
      (D t).ricci (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    (∀ q i j, ContDiffOn ℝ k
      (fun p : ℝ × V => iteratedFDeriv ℝ q (G p.1 i j) p.2)
      (J ×ˢ c.target)) →
    ∀ q i j, ContDiffOn ℝ k
      (fun p : ℝ × V => iteratedFDeriv ℝ q (R p.1 i j) p.2)
      (J ×ˢ c.target) := by
  classical
  dsimp only
  intro hjets
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := fun (t : ℝ) (i j : Fin n) (z : V) =>
    (g t).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
  let A := fun (t : ℝ) (z : V) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 (c.symm z) x0 (c.symm z) ((g t).inner (c.symm z))
  let H := fun (t : ℝ) (i j : Fin n) (z : V) =>
    (A t z).inverse (EuclideanSpace.proj j) i
  let Gamma := fun (t : ℝ) (i j l : Fin n) (z : V) =>
    theta l (c.symm z) ((D t).connection (E j) (c.symm z) (E i (c.symm z)))
  let br := fun (i j l : Fin n) (z : V) =>
    theta l (c.symm z) (VectorField.mlieBracket (𝓡 n) (E i) (E j) (c.symm z))
  let K := fun (t : ℝ) (i j l : Fin n) (z : V) =>
    fderiv ℝ (G t j l) z (EuclideanSpace.single i 1) +
    fderiv ℝ (G t l i) z (EuclideanSpace.single j 1) -
    fderiv ℝ (G t i j) z (EuclideanSpace.single l 1) +
    (∑ p : Fin n, br i j p z * G t p l z) -
    (∑ p : Fin n, br i l p z * G t j p z) -
    (∑ p : Fin n, br j l p z * G t i p z)
  let R := fun (t : ℝ) (i j k l : Fin n) (z : V) =>
    fderiv ℝ (Gamma t j k l) z (EuclideanSpace.single i 1) -
    fderiv ℝ (Gamma t i k l) z (EuclideanSpace.single j 1) +
    (∑ p : Fin n, Gamma t j k p z * Gamma t i p l z) -
    (∑ p : Fin n, Gamma t i k p z * Gamma t j p l z) -
    (∑ p : Fin n, br i j p z * Gamma t p k l z)
  let Ric := fun (t : ℝ) (i j : Fin n) (z : V) =>
    (D t).ricci (c.symm z) (E i (c.symm z)) (E j (c.symm z))
  let Reg (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B]
      (f : ℝ → V → B) : Prop :=
    (∀ t ∈ J, ContDiffOn ℝ ∞ (f t) c.target) ∧
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : ℝ × V => iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ c.target)
  have hcomp {B C : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      [NormedAddCommGroup C] [NormedSpace ℝ C]
      {f : ℝ → V → B} (hf : Reg B f) (Phi : B → C) (hPhi : ContDiff ℝ ∞ Phi) :
      Reg C (fun t x => Phi (f t x)) := by
    refine ⟨fun t ht => hPhi.comp_contDiffOn (hf.1 t ht), ?_⟩
    exact contDiffOn_spatial_jets_comp c.open_target isOpen_univ k f Phi hf.1
      hPhi.contDiffOn (fun _ _ _ _ => mem_univ _) hf.2
  have hprod {B C : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      [NormedAddCommGroup C] [NormedSpace ℝ C]
      {f : ℝ → V → B} {h : ℝ → V → C} (hf : Reg B f) (hh : Reg C h) :
      Reg (B × C) (fun t x => (f t x, h t x)) :=
    ⟨fun t ht => (hf.1 t ht).prodMk (hh.1 t ht),
      contDiffOn_spatial_jets_prodMk c.open_target k f h hf.1 hh.1 hf.2 hh.2⟩
  have hfixed {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      (f : V → B) (hf : ContDiffOn ℝ ∞ f c.target) : Reg B (fun _ => f) := by
    refine ⟨fun _ _ => hf, ?_⟩
    intro q
    have hq : ContDiffOn ℝ k (iteratedFDeriv ℝ q f) c.target := by
      intro z hz
      exact ((hf.contDiffAt (c.open_target.mem_nhds hz)).iteratedFDeriv_right
        (show (k : ℕ∞ω) + q ≤ ∞ by
          exact_mod_cast (le_top : (k : ℕ∞) + q ≤ ⊤))).contDiffWithinAt
    exact hq.comp contDiffOn_snd (fun _ hp => hp.2)
  have hconst {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (v : B) :
      Reg B (fun _ _ => v) := hfixed (fun _ => v) contDiffOn_const
  have hadd {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      {f h : ℝ → V → B} (hf : Reg B f) (hh : Reg B h) :
      Reg B (fun t x => f t x + h t x) :=
    hcomp (hprod hf hh) (fun p : B × B => p.1 + p.2) (contDiff_fst.add contDiff_snd)
  have hsub {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      {f h : ℝ → V → B} (hf : Reg B f) (hh : Reg B h) :
      Reg B (fun t x => f t x - h t x) :=
    hcomp (hprod hf hh) (fun p : B × B => p.1 - p.2) (contDiff_fst.sub contDiff_snd)
  have hmul {f h : ℝ → V → ℝ} (hf : Reg ℝ f) (hh : Reg ℝ h) :
      Reg ℝ (fun t x => f t x * h t x) :=
    hcomp (hprod hf hh) (fun p : ℝ × ℝ => p.1 * p.2) (contDiff_fst.mul contDiff_snd)
  have hsum {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      (f : Fin n → ℝ → V → B) (hf : ∀ i, Reg B (f i)) :
      Reg B (fun t x => ∑ i, f i t x) := by
    have hs (s : Finset (Fin n)) : Reg B (fun t x => ∑ i ∈ s, f i t x) := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using hconst (0 : B)
      | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi] using hadd (hf i) ih
    exact hs Finset.univ
  have hcongr {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      {f h : ℝ → V → B} (hf : Reg B f)
      (heq : ∀ t ∈ J, EqOn (h t) (f t) c.target) : Reg B h := by
    refine ⟨fun t ht => (hf.1 t ht).congr (heq t ht), ?_⟩
    intro q
    apply (hf.2 q).congr
    intro p hp
    have hevent : Function.uncurry h =ᶠ[𝓝 p] Function.uncurry f := by
      filter_upwards [(hJ.prod c.open_target).mem_nhds hp] with z hz
      exact heq z.1 hz.1 hz.2
    have hslice : h p.1 =ᶠ[𝓝 p.2] f p.1 :=
      hevent.comp_tendsto (continuousAt_const.prodMk continuousAt_id).tendsto
    exact (hslice.iteratedFDeriv ℝ q).eq_of_nhds
  have hderiv {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
      {f : ℝ → V → B} (hf : Reg B f) :
      Reg (V →L[ℝ] B) (fun t => fderiv ℝ (f t)) :=
    ⟨fun t ht => (hf.1 t ht).fderiv_of_isOpen c.open_target (by simp),
      contDiffOn_spatial_jets_fderiv k f hf.2⟩
  have hpartial {f : ℝ → V → ℝ} (hf : Reg ℝ f) (v : V) :
      Reg ℝ (fun t x => fderiv ℝ (f t) x v) :=
    hcomp (hderiv hf) (fun L : V →L[ℝ] ℝ => L v)
      (contDiff_id.clm_apply contDiff_const)
  have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hfamily (t : ℝ) : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g t) univ :=
    ((g t).contMDiff.comp contMDiff_snd).contMDiffOn
  have hG (i j : Fin n) : Reg ℝ (fun t => G t i j) := by
    refine ⟨?_, fun q => hjets q i j⟩
    intro t _
    have hp := (contMDiffOn_family_metric_pair (hfamily t) (E i) (E j) (hE i) (hE j)).comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact (hp.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
      (fun z hz => hbase hz)).contDiffOn
  let P : Fin n → Fin n → V →L[ℝ] V →L[ℝ] ℝ :=
    fun i j => (EuclideanSpace.proj i).smulRight (EuclideanSpace.proj j)
  have hEvalue {y : M} (hy : y ∈ e.baseSet) (i : Fin n) :
      E i y = e.symmL ℝ y (cb i) := by
    dsimp only [E]
    rw [e.localFrame_apply_of_mem_baseSet cb hy]
    simp only [Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply]
    exact (Trivialization.symmL_apply (R := ℝ) e hy (cb i)).symm
  have hAeq (t : ℝ) {z : V} (hz : z ∈ c.target) :
      A t z = ∑ i : Fin n, ∑ j : Fin n, G t i j z • P i j := by
    have hcoeff (i j : Fin n) : A t z (cb i) (cb j) = G t i j z := by
      dsimp only [A]
      rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) (hbase hz) (hbase hz) (by simp)]
      rw [← Trivialization.symmL_apply (R := ℝ) e (hbase hz) (cb i),
        ← Trivialization.symmL_apply (R := ℝ) e (hbase hz) (cb j)]
      simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
        LinearMap.id_coe, id_eq, ← hEvalue (hbase hz)]
      rfl
    apply ContinuousLinearMap.coe_injective
    apply cb.ext
    intro i
    apply ContinuousLinearMap.coe_injective
    apply cb.ext
    intro j
    change A t z (cb i) (cb j) = _
    rw [hcoeff]
    simp [P, cb, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hscale (i j : Fin n) : ContDiff ℝ ∞ (fun a : ℝ => a • P i j) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ℝ)
      (F := V →L[ℝ] V →L[ℝ] ℝ)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (P i j))
  have hA : Reg (V →L[ℝ] V →L[ℝ] ℝ) A := by
    apply hcongr (hsum (fun i t z => ∑ j, G t i j z • P i j) (fun i =>
      hsum (fun j t z => G t i j z • P i j) (fun j =>
        hcomp (hG i j) (fun a : ℝ => a • P i j)
          (hscale i j))))
    intro t _ z hz
    exact hAeq t hz
  have hAi (t : ℝ) {z : V} (hz : z ∈ c.target) : (A t z).IsInvertible :=
    (contMDiffOn_family_metric_frame_inverse (hfamily t) x0).1 (0, c.symm z) (hbase hz)
  have hI : Reg ((V →L[ℝ] ℝ) →L[ℝ] V) (fun t z => (A t z).inverse) := by
    refine ⟨?_, contDiffOn_spatial_jets_inverse c.open_target k A hA.1
      (fun t _ z hz => hAi t hz) hA.2⟩
    intro t ht z hz
    exact ((hAi t hz).contDiffAt_map_inverse.comp z
      ((hA.1 t ht).contDiffAt (c.open_target.mem_nhds hz))).contDiffWithinAt
  have hH (i j : Fin n) : Reg ℝ (fun t => H t i j) := by
    exact hcomp hI (fun L : (V →L[ℝ] ℝ) →L[ℝ] V =>
      (EuclideanSpace.proj i : V →L[ℝ] ℝ) (L (EuclideanSpace.proj j)))
      ((EuclideanSpace.proj i : V →L[ℝ] ℝ).contDiff.comp
        (contDiff_id.clm_apply contDiff_const))
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  have hbr (i j l : Fin n) : Reg ℝ (fun _ => br i j l) := by
    have hb : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (VectorField.mlieBracket (𝓡 n) (E i) (E j))) e.baseSet := by
      intro y hy
      exact (((hE i).contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (m := ⊤) (n := ⊤)
        ((hE j).contMDiffAt (e.open_baseSet.mem_nhds hy)) (by simp)).contMDiffWithinAt
    have hc := contMDiffOn_localFrameCoeff cb e.open_baseSet subset_rfl hb l
    apply hfixed
    exact (hc.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
      (fun z hz => hbase hz)).contDiffOn
  have hK (i j l : Fin n) : Reg ℝ (fun t => K t i j l) :=
    hsub (hsub (hadd
      (hsub (hadd (hpartial (hG j l) (EuclideanSpace.single i 1))
          (hpartial (hG l i) (EuclideanSpace.single j 1)))
        (hpartial (hG i j) (EuclideanSpace.single l 1)))
      (hsum (fun p t z => br i j p z * G t p l z) (fun p => hmul (hbr i j p) (hG p l))))
      (hsum (fun p t z => br i l p z * G t j p z) (fun p => hmul (hbr i l p) (hG j p))))
      (hsum (fun p t z => br j l p z * G t i p z) (fun p => hmul (hbr j l p) (hG i p)))
  have hGamma (i j l : Fin n) : Reg ℝ (fun t => Gamma t i j l) := by
    apply hcongr (hmul (hconst (1 / 2 : ℝ))
      (hsum (fun p t z => H t l p z * K t i j p z) (fun p => hmul (hH l p) (hK i j p))))
    intro t _ z hz
    exact connection_frame_coordinates_eq_inverse_koszul (D t) x0 z hz i j l
  have hR (i j a l : Fin n) : Reg ℝ (fun t => R t i j a l) :=
    hsub (hsub (hadd
      (hsub (hpartial (hGamma j a l) (EuclideanSpace.single i 1))
        (hpartial (hGamma i a l) (EuclideanSpace.single j 1)))
      (hsum (fun p t z => Gamma t j a p z * Gamma t i p l z)
        (fun p => hmul (hGamma j a p) (hGamma i p l))))
      (hsum (fun p t z => Gamma t i a p z * Gamma t j p l z)
        (fun p => hmul (hGamma i a p) (hGamma j p l))))
      (hsum (fun p t z => br i j p z * Gamma t p a l z)
        (fun p => hmul (hbr i j p) (hGamma p a l)))
  have hRic (i j : Fin n) : Reg ℝ (fun t => Ric t i j) := by
    apply hcongr (hsum (fun p t z => R t p i j p z) (fun p => hR p i j p))
    intro t _ z hz
    exact (curvature_and_ricci_frame_coordinates_eq_connection_coefficients
      (D t) x0 z hz).2 i j
  intro q i j
  exact (hRic i j).2 q

end NativeFiniteRegularity

end PoincareConjecture.RicciFlow.Local
