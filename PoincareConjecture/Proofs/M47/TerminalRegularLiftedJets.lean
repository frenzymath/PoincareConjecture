import PoincareConjecture.Proofs.M47.TerminalGermsUniverseMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Geometry.Manifold.LocalDiffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_regular_lifted_chart_jets
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] (g : RiemannianMetric 3 X)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞) :
    letI : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
    letI : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
    let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    let cL := d.toPartialDiffeomorph.trans c
    cL.source = ULift.down ⁻¹' c.source ∧ cL.target = c.target ∧
      (cL.symm : E → ULift.{u} X) = ULift.up ∘ c.symm ∧
      ∀ m x, x ∈ c.target →
        iteratedFDeriv ℝ m (gL.pullbackCoefficients cL.symm) x =
          iteratedFDeriv ℝ m (g.pullbackCoefficients c.symm) x := by
  let : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
  let : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
  let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  let cL := d.toPartialDiffeomorph.trans c
  have hs : cL.source = ULift.down ⁻¹' c.source := by
    change univ ∩ ULift.down ⁻¹' c.source = _
    exact univ_inter _
  have ht : cL.target = c.target := by
    change c.target ∩ c.symm ⁻¹' univ = _
    simp only [preimage_univ, inter_univ]
  have hinv : (cL.symm : E → ULift.{u} X) = ULift.up ∘ c.symm := rfl
  have heq : EqOn (gL.pullbackCoefficients cL.symm)
      (g.pullbackCoefficients c.symm) c.target := by
    intro x hx
    have hcs := c.symm.mdifferentiableAt (by simp) hx
    have hls : MDifferentiableAt (𝓡 3) (𝓡 3) cL.symm x :=
      (d.symm.mdifferentiable (by simp) _).comp x hcs
    have hid : d ∘ (cL.symm : E → ULift.{u} X) = (c.symm : E → X) := by
      funext y
      exact d.apply_symm_apply (c.symm y)
    have hd := mfderiv_comp x (d.mdifferentiable (by simp) _) hls
    rw [hid] at hd
    ext v w
    change g.inner (d (d.symm (c.symm x)))
      (mfderiv (𝓡 3) (𝓡 3) d (cL.symm x)
        (mfderiv (𝓡 3) (𝓡 3) cL.symm x v))
      (mfderiv (𝓡 3) (𝓡 3) d (cL.symm x)
        (mfderiv (𝓡 3) (𝓡 3) cL.symm x w)) = _
    rw [d.apply_symm_apply]
    exact congrArg₂ (fun v w => g.inner (c.symm x) v w)
      (congrArg (fun A => A v) hd.symm) (congrArg (fun A => A w) hd.symm)
  refine ⟨hs, ht, hinv, ?_⟩
  intro m x hx
  have hgerm : gL.pullbackCoefficients cL.symm =ᶠ[𝓝 x]
      g.pullbackCoefficients c.symm := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact heq hy
  exact (hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds



theorem terminalSource_regular_lifted_source_jets
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] (g : RiemannianMetric 3 X)
    {Y : ℕ → Type w} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace E (Y k)]
    [∀ k, IsManifold (𝓡 3) ∞ (Y k)] (gk : ∀ k, RiemannianMetric 3 (Y k))
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (Y k) ∞)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gk k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    letI : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
    letI : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
    let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    let phiL := fun k => d.toPartialDiffeomorph.trans (phi k)
    let cL := fun i => d.toPartialDiffeomorph.trans (c i)
    (∀ k, (phiL k).source = ULift.down ⁻¹' (phi k).source) ∧
      (∀ i k, phiL k ∘ (cL i).symm = phi k ∘ (c i).symm) ∧
      ∀ i m K, IsCompact K → K ⊆ (cL i).target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((gk k).pullbackCoefficients (phiL k ∘ (cL i).symm)))
        (iteratedFDeriv ℝ m (gL.pullbackCoefficients (cL i).symm)) atTop K := by
  let : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
  let : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
  let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  let phiL := fun k => d.toPartialDiffeomorph.trans (phi k)
  let cL := fun i => d.toPartialDiffeomorph.trans (c i)
  have hsource (k : ℕ) : (phiL k).source = ULift.down ⁻¹' (phi k).source := by
    change univ ∩ ULift.down ⁻¹' (phi k).source = _
    exact univ_inter _
  have hmaps (i k : ℕ) : phiL k ∘ (cL i).symm = phi k ∘ (c i).symm := rfl
  refine ⟨hsource, hmaps, ?_⟩
  intro i m K hK hKi
  have hc := terminalSource_regular_lifted_chart_jets.{u} g (c i)
  have hKc : K ⊆ (c i).target := hc.2.1 ▸ hKi
  change TendstoUniformlyOn
    (fun k => iteratedFDeriv ℝ m ((gk k).pullbackCoefficients (phiL k ∘ (cL i).symm)))
    (iteratedFDeriv ℝ m (gL.pullbackCoefficients (cL i).symm)) atTop K
  simp_rw [hmaps]
  exact (hjet i m K hK hKc).congr_right
    (fun x hx => (hc.2.2.2 m x (hKc hx)).symm)



theorem terminalSource_regular_lifted_exhaustion
    {X : Type v} [TopologicalSpace X] (V : ℕ → Set X)
    (hopen : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcompact : ∀ k, IsCompact (closure (V k)))
    (hcover : (⋃ k, V k) = univ) (p : X) (hp : ∀ k, p ∈ V k) :
    let VL : ℕ → Set (ULift.{u} X) := fun k => ULift.down ⁻¹' V k
    (∀ k, IsOpen (VL k)) ∧ Monotone VL ∧
      (∀ k, IsCompact (closure (VL k))) ∧ (⋃ k, VL k) = univ ∧
      ∀ k, ULift.up p ∈ VL k := by
  let VL : ℕ → Set (ULift.{u} X) := fun k => ULift.down ⁻¹' V k
  refine ⟨fun k => (hopen k).preimage Homeomorph.ulift.continuous, ?_, ?_, ?_, hp⟩
  · exact fun i j hij => preimage_mono (hmono hij)
  · intro k
    change IsCompact (closure ((Homeomorph.ulift : ULift.{u} X ≃ₜ X) ⁻¹' V k))
    rw [← Homeomorph.ulift.preimage_closure]
    exact Homeomorph.ulift.isCompact_preimage.mpr (hcompact k)
  · change (⋃ k, ULift.down ⁻¹' V k) = univ
    rw [← preimage_iUnion, hcover, preimage_univ]

end PoincareConjecture.M47
