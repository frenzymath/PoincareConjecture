import PoincareConjecture.Proofs.M47.TerminalRegularStageFamily
import PoincareConjecture.Proofs.M47.TerminalRegularAtlasCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSource_regular_included_metric
    {S : RepairedControlledSchedulesData.{u}}
    {B : M47ComponentAnalyticBounds.{u} S.setup.C} {p : SurgeryParameterPrefix S.constants}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {W : M33RegularHistoryWindow F}
    {H : M33RegularHistoryData W} {base Q r A tau0 tau K L a R rho : ℝ} {N : ℕ}
    {center : (F.slice base).carrier}
    (data : TerminalRegularStageData S B p O H base Q r A tau0 tau K L a R rho N center) :
    let U := terminalRegularStageSource F base Q A center
    let e := terminalSourceNormal_historyCylinder H U data.time data.cylinder
    ∀ s hs (z : U) (v w : TangentSpace (𝓡 3) z),
      (data.flow.metric s).inner z v w = e.pullbackInner s hs z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w) := by
  dsimp only
  intro s hs z v w
  exact (data.metric s hs z v w).trans
    ((terminalSourceNormal_historyCylinder_maps H _ data.time data.cylinder).2
      s hs z.val z.property _ _).symm

theorem terminalSource_regular_captured_jets
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {Y : ℕ → Type u} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace E (Y k)]
    [∀ k, IsManifold (𝓡 3) ∞ (Y k)]
    {M : ℕ → Type w} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    (g : RiemannianMetric 3 X) (gY : ∀ k, RiemannianMetric 3 (Y k))
    (gM : ∀ k, RiemannianMetric 3 (M k))
    (V : ℕ → Set X) (hV : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcover : (⋃ k, V k) = univ)
    (j : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) (Y k) (M k) ∞)
    (hj : ∀ k, (j k).source = univ)
    (hmetric : ∀ k z (v w : TangentSpace (𝓡 3) z),
      (gY k).inner z v w = (gM k).inner (j k z)
        (mfderiv (𝓡 3) (𝓡 3) (j k) z v) (mfderiv (𝓡 3) (𝓡 3) (j k) z w))
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (Y k) ∞)
    (hsource : ∀ k, (phi k).source = V k) (f : ∀ k, X → M k)
    (hfactor : ∀ k x, x ∈ V k → j k (phi k x) = f k x)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hjets : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gM k).pullbackCoefficients (f k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((gY k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K := by
  intro i m K hK hKU
  have hC : IsCompact ((c i).symm '' K) :=
    hK.image_of_continuousOn ((c i).symm.contMDiffOn_toFun.continuousOn.mono hKU)
  obtain ⟨k0, hk0⟩ := hC.elim_directed_cover V hV
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  apply (hjets i m K hK hKU).congr
  filter_upwards [eventually_ge_atTop k0] with k hk y hy
  have hcapture : (c i).symm y ∈ (phi k).source := by
    rw [hsource k]
    exact hmono hk (hk0 ⟨y, hy, rfl⟩)
  exact (terminalSource_atlas_inverse_coefficient_jets (gY k) (gM k) (j k) (hj k)
    (hmetric k) (phi k) (f k) (fun x hx => hfactor k x ((hsource k) ▸ hx))
    (c i) (hKU hy) hcapture).2 m |>.symm

end PoincareConjecture.M47
