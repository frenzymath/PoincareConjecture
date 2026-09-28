import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularPair
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.LevelComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData
private theorem normalized_level_geometry
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
    {g : RiemannianMetric (n+1) M} (D : LeviCivitaData g)
    {u h : M → ℝ}
    (hu : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ u)
    (hh : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h)
    (U : TopologicalSpace.Opens M) (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (n+1)) x), -1 ≤ D.sectionalCurvature x v w)
    {r τ : ℝ} (hr : 0<r) (hrhalf : r≤1/2) (hτhalf : (1/2:ℝ)≤τ) (hτ1 : τ≤1)
    (p : M) (t : ℝ)
    (hinside : ∀ x, u x=t → x∈g.ball p (2*r))
    (hbuffer : ∀ x, u x=t →
      {y | g.edist x y ≤ ENNReal.ofReal ((τ*r/1024)/16)} ⊆ U)
    (hgrad : ∀ x∈U, (1/2:ℝ)≤g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x)≤1 ∧
      (1/2:ℝ)≤g.tangentNorm x (D.gradient h x) ∧
      g.tangentNorm x (D.gradient h x)≤1 ∧
      g.inner x (D.gradient u x) (D.gradient h x)≤ -(1/8:ℝ) ∧
      ∀ v:TangentSpace (𝓡 (n+1)) x,
        D.hessian u x v v≤(3/(τ*r/1024))*g.inner x v v ∧
        D.hessian h x v v≤(3/(τ*r/1024))*g.inner x v v) :
    let c : ℝ := ((2*r)^2)⁻¹
    let hc' : 0<c := by dsimp [c]; positivity
    let G := rescaledMetric g c hc'
    let u' := fun x => Real.sqrt c * u x
    let hu' : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ u' := contMDiff_const.mul hu
    ∃ hreg : ∀ x∈U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) u' x ≠ 0,
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openLevelSetChartedSpace hu' U hreg n (Real.sqrt c*t)
      letI := isManifold_openLevelSet hu' U hreg n (Real.sqrt c*t)
      let L := openLevelSet u' U (Real.sqrt c*t)
      let gL := G.regularLevelMetric hu' U hreg (Real.sqrt c*t)
      let N := ⌈RiemannianMetric.modelVolume (n+1) 1 3 /
        RiemannianMetric.modelVolume (n+1) 1 (1/10485760)⌉₊
      MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
        Nat.card (ConnectedComponents L)≤N ∧
        ∀ x y:L, y∈connectedComponent x →
          gL.edist x y≤ENNReal.ofReal ((N:ℝ)*18*Real.exp (3/10)) := by
  let c : ℝ := ((2*r)^2)⁻¹
  have hc' : 0<c := by dsimp [c]; positivity
  let G := rescaledMetric g c hc'
  let DS := rescaledMetric_connection g D c hc'
  let u' := fun x => Real.sqrt c*u x
  let h' := fun x => Real.sqrt c*h x
  have hu' : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ u' := contMDiff_const.mul hu
  have hh' : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h' := contMDiff_const.mul hh
  have hτ : 0<τ := by linarith
  have hsqrt : Real.sqrt c=(2*r)⁻¹ := by
    dsimp [c]
    rw [Real.sqrt_inv,Real.sqrt_sq (by positivity)]
  have hsqrtpos : 0<Real.sqrt c := Real.sqrt_pos.mpr hc'
  have hlev (x:M) : u' x=Real.sqrt c*t ↔ u x=t := by
    change Real.sqrt c * u x = Real.sqrt c * t ↔ u x = t
    constructor
    · exact mul_left_cancel₀ hsqrtpos.ne'
    · exact congrArg (fun z => Real.sqrt c * z)
  have hGr (x y:M) : G.edist x y = ENNReal.ofReal ((2*r)⁻¹)*g.edist x y := by
    rw [rescaledMetric_edist,hsqrt]
  have hsecG : ∀ x (v w:TangentSpace (𝓡 (n+1)) x),
      -1≤DS.sectionalCurvature x v w := by
    intro x v w
    rw [rescaledMetric_sectionalCurvature]
    dsimp [c]
    rw [inv_inv]
    have he := mul_le_mul_of_nonneg_left (hsec x v w) (sq_nonneg (2*r))
    nlinarith
  have hH : 0≤6144/τ := by positivity
  have hρ : 0<τ/2621440 := by positivity
  have hρ1 : τ/2621440≤1 := by linarith
  have hscale : (3/(τ*r/1024))/Real.sqrt c=6144/τ := by
    rw [hsqrt]
    field_simp [hr.ne', hτ.ne']
    ring
  have hgU (x:M) (hx:x∈U) :
      (1/2:ℝ)≤G.tangentNorm x (DS.gradient u' x) ∧
      G.tangentNorm x (DS.gradient u' x)≤1 := by
    rw [show DS.gradient u' x = G.gradient u' x from rfl,
      rescaledMetric_tangentNorm_gradient_sqrt_mul]
    exact ⟨(hgrad x hx).1,(hgrad x hx).2.1⟩
  have hgH (x:M) (hx:x∈U) :
      (1/2:ℝ)≤G.tangentNorm x (DS.gradient h' x) ∧
      G.tangentNorm x (DS.gradient h' x)≤1 := by
    rw [show DS.gradient h' x = G.gradient h' x from rfl,
      rescaledMetric_tangentNorm_gradient_sqrt_mul]
    exact ⟨(hgrad x hx).2.2.1,(hgrad x hx).2.2.2.1⟩
  have hp (x:M) (hx:x∈U) :
      G.inner x (DS.gradient u' x) (DS.gradient h' x)≤ -(1/8:ℝ) := by
    change G.inner x (G.gradient u' x) (G.gradient h' x)≤_
    rw [rescaledMetric_inner_gradient_sqrt_mul]
    exact (hgrad x hx).2.2.2.2.1
  have hhu (x:M) (hx:x∈U) (v:TangentSpace (𝓡 (n+1)) x) :
      DS.hessian u' x v v≤(6144/τ)*G.inner x v v := by
    simpa only [hscale] using rescaledMetric_hessian_sqrt_mul_le g D c hc' u x v
      (3/(τ*r/1024)) ((hgrad x hx).2.2.2.2.2 v).1
  have hhh (x:M) (hx:x∈U) (v:TangentSpace (𝓡 (n+1)) x) :
      DS.hessian h' x v v≤(6144/τ)*G.inner x v v := by
    simpa only [hscale] using rescaledMetric_hessian_sqrt_mul_le g D c hc' h x v
      (3/(τ*r/1024)) ((hgrad x hx).2.2.2.2.2 v).2
  have hinsideG (x:M) (hx:u' x=Real.sqrt c*t) : x∈G.ball p 1 := by
    rw [rescaledMetric_ball,hsqrt]
    simpa only [div_inv_eq_mul,one_mul] using hinside x ((hlev x).mp hx)
  have hbufferG (x:M) (hx:u' x=Real.sqrt c*t) :
      {y | G.edist x y≤ENNReal.ofReal (80*(τ/2621440))}⊆U := by
    intro y hy
    apply hbuffer x ((hlev x).mp hx)
    have ha : 0<2*r := by positivity
    have he := mul_le_mul' (le_refl (ENNReal.ofReal (2*r))) hy
    rw [hGr,←mul_assoc,←ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne',
      ENNReal.ofReal_one,one_mul,←ENNReal.ofReal_mul ha.le] at he
    change g.edist x y ≤ ENNReal.ofReal _
    convert he using 1 <;> congr 1 <;> ring
  obtain ⟨hreg,hcompleteL,hfinite,hcard,hdiam⟩ :=
    DS.regularLevel_components_and_diameter_of_opposite_gradients hu' hh' U
      hH hρ hρ1 hgU hgH hp (fun x hx v _ => hhu x hx v) (fun x hx v _ => hhh x hx v)
      (metricComplete_rescaledMetric g c hc' hc) hsecG p (Real.sqrt c*t)
      hinsideG hbufferG
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hu' U hreg n (Real.sqrt c*t)
  let := isManifold_openLevelSet hu' U hreg n (Real.sqrt c*t)
  have hden : RiemannianMetric.modelVolume (n+1) 1 (1/10485760) ≤
      RiemannianMetric.modelVolume (n+1) 1 ((τ/2621440)/2) :=
    RiemannianMetric.modelVolume_mono_radius (n+1) (by norm_num)
      (by norm_num) (by linarith)
  have hcount : ⌈RiemannianMetric.modelVolume (n+1) 1 3 /
      RiemannianMetric.modelVolume (n+1) 1 ((τ/2621440)/2)⌉₊ ≤
      ⌈RiemannianMetric.modelVolume (n+1) 1 3 /
        RiemannianMetric.modelVolume (n+1) 1 (1/10485760)⌉₊ := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_left
      (RiemannianMetric.modelVolume_nonneg (n+1) (by norm_num) (by norm_num))
      (RiemannianMetric.modelVolume_pos (by omega : 1≤n+1) (by norm_num) (by norm_num)) hden
  refine ⟨hreg,hcompleteL,hfinite,hcard.trans hcount,?_⟩
  intro x y hxy
  apply (hdiam x y hxy).trans
  apply ENNReal.ofReal_le_ofReal
  have hnum : 128*(6144/τ)*(τ/2621440)=(3/10:ℝ) := by field_simp [hτ.ne']; ring
  rw [hnum]
  have hcountR : (⌈RiemannianMetric.modelVolume (n+1) 1 3 /
      RiemannianMetric.modelVolume (n+1) 1 ((τ/2621440)/2)⌉₊:ℝ) ≤
      ⌈RiemannianMetric.modelVolume (n+1) 1 3 /
        RiemannianMetric.modelVolume (n+1) 1 (1/10485760)⌉₊ := by exact_mod_cast hcount
  have hsmall : 18*(τ/2621440)≤18 := by linarith
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcountR
      (show 0≤18*(τ/2621440)*Real.exp (3/10) by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (3/10)).le) (Nat.cast_nonneg _)
    _ = _ := by ring
end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric
private theorem transfer_rescaled_level_geometry
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
    (g : RiemannianMetric (n+1) M) (hc : MetricComplete g)
    {F v : M → ℝ} (hF : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ F)
    (hv : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ v)
    (U : TopologicalSpace.Opens M)
    (hregv : ∀ x∈U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) v x≠0)
    {t d r c : ℝ} (hr : 0<r) (hc' : 0<c) (hsqrt : Real.sqrt c=(2*r)⁻¹)
    (hregF : ∀ x, F x=t → mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) F x≠0)
    (he : ∀ x, F x=t ↔ x∈U ∧ v x=d)
    (N : ℕ)
    (hfinite : Finite (ConnectedComponents (openLevelSet v U d)))
    (hcard : Nat.card (ConnectedComponents (openLevelSet v U d))≤N)
    (hdiam : letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openLevelSetChartedSpace hv U hregv n d
      letI := isManifold_openLevelSet hv U hregv n d
      ∀ x y:openLevelSet v U d, y∈connectedComponent x →
        ((rescaledMetric g c hc').regularLevelMetric hv U hregv d).edist x y≤
          ENNReal.ofReal ((N:ℝ)*18*Real.exp (3/10))) :
    let V := g.regularDomain hF
    let hreg := g.regularDomain_regular hF
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hF V hreg n t
    letI := isManifold_openLevelSet hF V hreg n t
    let L := openLevelSet F V t
    let gL := g.regularLevelMetric hF V hreg t
    MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
      Nat.card (ConnectedComponents L)≤N ∧
      ∀ x y:L, y∈connectedComponent x →
        gL.edist x y≤ENNReal.ofReal ((N:ℝ)*36*Real.exp (3/10)*r) := by
  let V := g.regularDomain hF
  let hreg := g.regularDomain_regular hF
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hF V hreg n t
  let := isManifold_openLevelSet hF V hreg n t
  let := openLevelSetChartedSpace hv U hregv n d
  let := isManifold_openLevelSet hv U hregv n d
  let L := openLevelSet F V t
  let gL := g.regularLevelMetric hF V hreg t
  have hlevelV : F ⁻¹' {t} ⊆ (V:Set M) := by
    intro x hx
    exact (g.mem_regularDomain_iff hF x).mpr (hregF x hx)
  have he' : ∀ x, (x∈V ∧ F x=t) ↔ (x∈U ∧ v x=d) := by
    intro x
    exact ⟨fun hx => (he x).mp hx.2, fun hx => ⟨hlevelV ((he x).mpr hx),(he x).mpr hx⟩⟩
  let e := openLevelDiffeomorphOfEq hF hv n hreg hregv he'
  have hsurj := e.symm.contMDiff.continuous.connectedComponentsMap_surjective e.symm.surjective
  let := hfinite
  have hfin : Finite (ConnectedComponents L) :=
    Finite.of_surjective _ hsurj
  have hcount : Nat.card (ConnectedComponents L)≤N :=
    (Nat.card_le_card_of_surjective _ hsurj).trans hcard
  have hemb : Topology.IsClosedEmbedding (openLevelIncl F V t) := by
    refine ⟨isEmbedding_openLevelIncl F V t,?_⟩
    rw [range_openLevelIncl,inter_eq_right.mpr hlevelV]
    exact isClosed_singleton.preimage hF.continuous
  refine ⟨metricComplete_of_isClosedEmbedding gL g
    (contMDiff_openLevelIncl hF V hreg n t) hemb
    (g.regularLevelMetric_inner hF V hreg t) hc,hfin,hcount,?_⟩
  intro x y hxy
  have hexy := hdiam (e x) (e y) (e.contMDiff.continuous.mapsTo_connectedComponent x hxy)
  have hedist := regularLevelMetric_edist_equivOfEq hF hv hreg hregv he'
    (rescaledMetric g c hc') x y
  change ((rescaledMetric g c hc').regularLevelMetric hv U hregv d).edist
    (e x) (e y) = _ at hedist
  rw [hedist,regularLevelMetric_rescaledMetric_edist,hsqrt] at hexy
  have ha : 0<2*r := by positivity
  have hb := mul_le_mul' (le_refl (ENNReal.ofReal (2*r))) hexy
  rw [←mul_assoc,←ENNReal.ofReal_mul ha.le,mul_inv_cancel₀ ha.ne',
    ENNReal.ofReal_one,one_mul,←ENNReal.ofReal_mul ha.le] at hb
  convert hb using 1 <;> congr 1 <;> ring
end PoincareConjecture.RiemannianMetric

theorem PoincareConjecture.RiemannianMetric.regularLevel_geometry_of_annular_opposite_partner
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
    (g : RiemannianMetric (n+1) M) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w:TangentSpace (𝓡 (n+1)) x), -1≤D.sectionalCurvature x v w)
    {F u h : M → ℝ}
    (hF : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ F)
    (hu : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ u)
    (hh : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ h)
    (U : TopologicalSpace.Opens M) {r τ : ℝ}
    (hr : 0<r) (hrhalf : r≤1/2) (hτhalf : (1/2:ℝ)≤τ) (hτ1 : τ≤1)
    (hFu : ∀ x, F x=u x/(2*τ)) (p:M) (t:ℝ)
    (hregF : ∀ x, F x=t → mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) F x≠0)
    (hinside : ∀ x, F x=t → x∈g.ball p (2*r))
    (hbuffer : ∀ x, F x=t →
      {y | g.edist x y≤ENNReal.ofReal ((τ*r/1024)/16)}⊆U)
    (hgrad : ∀ x∈U,
      (1/2:ℝ)≤g.tangentNorm x (D.gradient u x) ∧
      g.tangentNorm x (D.gradient u x)≤1 ∧
      (1/2:ℝ)≤g.tangentNorm x (D.gradient h x) ∧
      g.tangentNorm x (D.gradient h x)≤1 ∧
      g.inner x (D.gradient u x) (D.gradient h x)≤ -(1/8:ℝ) ∧
      ∀ v:TangentSpace (𝓡 (n+1)) x,
        D.hessian u x v v≤(3/(τ*r/1024))*g.inner x v v ∧
        D.hessian h x v v≤(3/(τ*r/1024))*g.inner x v v) :
    let V := g.regularDomain hF
    let hreg := g.regularDomain_regular hF
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1)))=n+1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hF V hreg n t
    letI := isManifold_openLevelSet hF V hreg n t
    let L := openLevelSet F V t
    let gL := g.regularLevelMetric hF V hreg t
    let N := ⌈modelVolume (n+1) 1 3 / modelVolume (n+1) 1 (1/10485760)⌉₊
    MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
      Nat.card (ConnectedComponents L)≤N ∧
      ∀ x y:L, y∈connectedComponent x →
        gL.edist x y≤ENNReal.ofReal ((N:ℝ)*36*Real.exp (3/10)*r) := by
  have hτ : 0<τ := by linarith
  have hFuLevel (x:M) : F x=t ↔ u x=2*τ*t := by
    rw [hFu x,div_eq_iff (by positivity : 2*τ≠0)]
    constructor <;> intro hx <;> nlinarith only [hx]
  obtain ⟨hreg,hcompleteN,hfinite,hcard,hdiam⟩ :=
    D.normalized_level_geometry hu hh U hc hsec hr hrhalf hτhalf hτ1 p (2*τ*t)
      (fun x hx => hinside x ((hFuLevel x).mpr hx))
      (fun x hx => hbuffer x ((hFuLevel x).mpr hx)) hgrad
  let c : ℝ := ((2*r)^2)⁻¹
  have hc' : 0<c := by dsimp [c]; positivity
  let v := fun x => Real.sqrt c*u x
  have hv : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ v := contMDiff_const.mul hu
  have hsqrt : Real.sqrt c=(2*r)⁻¹ := by
    dsimp [c]
    rw [Real.sqrt_inv,Real.sqrt_sq (by positivity)]
  have he (x:M) : F x=t ↔ x∈U ∧ v x=Real.sqrt c*(2*τ*t) := by
    constructor
    · intro hx
      refine ⟨hbuffer x hx ?_,?_⟩
      · simp only [Set.mem_ofPred_eq,RiemannianMetric.edist,Manifold.riemannianEDist_self]
        exact bot_le
      · dsimp [v]
        rw [(hFuLevel x).mp hx]
    · intro hx
      apply (hFuLevel x).mpr
      exact mul_left_cancel₀ (Real.sqrt_pos.mpr hc').ne' hx.2
  exact g.transfer_rescaled_level_geometry hc hF hv U hreg hr hc' hsqrt hregF he
    _ hfinite hcard hdiam

theorem PoincareConjecture.RiemannianMetric.exists_annular_slab_with_controlled_level_geometry
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (n + 1) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (n + 1)) x),
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r δ : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hascent : ∀ y : M, r / 2 < (g.edist p y).toReal →
      (g.edist p y).toReal < 3 * r → ∀ a : ℝ, 0 < a →
        ∃ z : M, (g.edist y z).toReal < a ∧
          (1 - δ ^ 2 / 8) * (g.edist y z).toReal <
            (g.edist p z).toReal - (g.edist p y).toReal) :
    let ε := δ ^ 4 * r / 1048576
    let I := Ioo (9 * r / 16) (15 * r / 16)
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (n + 1) 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume (n + 1) 1 (1 / 10485760)⌉₊
    ∃ F : M → ℝ, ∃ hF : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ F,
      IsProperMap (I.restrictPreimage F) ∧
      (∀ x : M, F x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) F x ≠ 0) ∧
      (∀ x : M, F x ∈ I →
        r < (g.edist p x).toReal ∧ (g.edist p x).toReal < 2 * r) ∧
      (∀ x : M, r < (g.edist p x).toReal → (g.edist p x).toReal < 2 * r →
        |F x - (g.edist p x).toReal / 2| ≤ ε / 2 ∧
        (1 / 4 : ℝ) ≤ g.tangentNorm x (D.gradient F x) ∧
        g.tangentNorm x (D.gradient F x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 (n + 1)) x,
          D.hessian F x v v ≤ (5 / r) * g.inner x v v) ∧
      F ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ g.ball p (2 * r) ∧
      {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
        F ⁻¹' Icc (7 * r / 12) (3 * r / 5) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact (F ⁻¹' {t}) ∧
        let U := g.regularDomain hF
        let hreg := g.regularDomain_regular hF
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openLevelSetChartedSpace hF U hreg n t
        letI := isManifold_openLevelSet hF U hreg n t
        let L := openLevelSet F U t
        let gL := g.regularLevelMetric hF U hreg t
        PoincareConjecture.MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
          Nat.card (ConnectedComponents L) ≤ N ∧
          ∀ x y : L, y ∈ connectedComponent x →
            gL.edist x y ≤ ENNReal.ofReal ((N : ℝ) * 36 * Real.exp (3 / 10) * r) := by
  classical
  let := g.toMetricSpace
  let τ : ℝ := 1/(1+δ^2/8)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hτ1 : τ≤1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg δ]
  have hτhalf : (1/2:ℝ)≤τ := by
    dsimp [τ]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨F,u,hF,hu,hFu,hproper,hregular,hcore,hbounds,hslab,hrad,hpartners⟩ :=
    g.exists_annular_slab_with_level_opposite_partners D hc hsec p hr
      (by linarith : r≤1) hδ hδsmall hascent
  refine ⟨F,hF,hproper,hregular,hcore,?_,hslab,hrad,?_⟩
  · intro x hx hx'
    exact ⟨(hbounds x hx hx').1,(hbounds x hx hx').2.1,
      (hbounds x hx hx').2.2.1,(hbounds x hx hx').2.2.2.1⟩
  intro t ht
  obtain ⟨hcompact,h,hh,hbuffer,hgrad⟩ := hpartners t ht
  refine ⟨hcompact,?_⟩
  let U : TopologicalSpace.Opens M :=
    ⟨u ⁻¹' Ioo (2*τ*t-(τ*r/1024)/4) (2*τ*t+(τ*r/1024)/4),
      isOpen_Ioo.preimage hu.continuous⟩
  apply g.regularLevel_geometry_of_annular_opposite_partner D hc hsec hF hu hh U
    hr hrhalf hτhalf hτ1 hFu p t
  · intro x hx
    apply hregular
    rw [hx]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · intro x hx
    apply hslab
    change F x∈Icc (55*r/96) (9*r/10)
    rw [hx]
    exact ⟨by linarith [ht.1],ht.2⟩
  · intro x hx y hy
    apply hbuffer x hx
    change dist y x≤(τ*r/1024)/16
    rw [dist_comm]
    change (g.edist x y).toReal≤_
    exact (ENNReal.toReal_le_toReal (g.edist_ne_top x y) ENNReal.ofReal_ne_top).mpr hy
      |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
  · intro x hx
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hgrad x hx
    exact ⟨h1,h2,h3,h4,by linarith,h6⟩
