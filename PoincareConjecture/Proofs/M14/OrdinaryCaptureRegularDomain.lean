import PoincareConjecture.Proofs.M14.OrdinaryCaptureDifferential
import PoincareConjecture.Proofs.M14.OrdinaryCaptureReverseBranches











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T3Space C] [ConnectedSpace C] [SecondCountableTopology C]
  [MeasurableSpace C] [BorelSpace C] {K : SpacetimeInterval}
  {e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C}
  {g : SpacetimeCylinderMetric e} {F : RicciFlow n C K.domain} {τmax : ℝ}
  (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
  (D : M14OrdinaryCaptureData G C K e g F t₀.val τmax)
  (hCoordinates : SpacetimeGaugeTheory.{u, u} G.leafwise G.timeIntervals)
  (hPath : M14PathCalculusConclusion G)

include D hCoordinates hPath




theorem ordinaryCapture_stable_of_regular
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialGeometry F t₀.val τmax c₀)
    (W : TangentSpace (𝓡 n) c₀) {τ : ℝ}
    (hreg : (W, τ) ∈ A.toLExponentialFamily.regularDomain) :
    M14StableInitialVector G t₀.val τ (e.toSpacetime (t₀, c₀)) E
      (g.spatialTangentEquiv t₀ c₀ W) := by
  have hlocal : (W, τ) ∈ A.toLExponentialFamily.localRegularDomain := by
    rw [← A.regular_domain_eq_local]
    exact hreg
  obtain ⟨hτ, hmax, hbij, N, hN, hWN, huniq⟩ := hlocal
  have htransport (V : TangentSpace (𝓡 n) c₀) (hV : V ∈ N) :=
    ordinaryCapture_unique_family_transport t₀ c₀ D hCoordinates hPath E
      A.toLExponentialFamily V (huniq V hV)
  have hvalid := (A.path W τ hτ hmax).time_mem τ ⟨hτ.le, le_rfl⟩
  have heq (V : TangentSpace (𝓡 n) c₀) (hV : V ∈ N) :
      E.gamma (g.spatialTangentEquiv t₀ c₀ V) (Real.sqrt τ) =
        e.toSpacetime (⟨t₀.val - τ, hvalid⟩, A.gamma V τ) := by
    have hclock := E.clock _ _ (htransport V hV).1.1
    have hr := ordinaryCapture_point_reconstruct D (htransport V hV).2.1
      ⟨t₀.val - τ, hvalid⟩ (by simpa only [Real.sq_sqrt hτ.le] using hclock)
    rw [(htransport V hV).2.2] at hr
    exact hr.symm
  have hW := (htransport W hWN).1.1
  have hd := (ordinaryCapture_differential_bijective_iff t₀ c₀ D hCoordinates E
    A.toLExponentialFamily hτ hmax hvalid W hW N hN hWN
    (fun V hV => (htransport V hV).1.1) heq).mpr hbij
  let L := g.spatialTangentEquiv t₀ c₀
  refine ⟨hW, hd, L '' N, L.toHomeomorph.isOpenMap N hN, ⟨W, hWN, rfl⟩, ?_⟩
  rintro Z ⟨V, hV, rfl⟩
  exact (htransport V hV).1




theorem ordinaryCapture_regular_of_stable
    (E : M14ExponentialFamily G t₀.val (e.toSpacetime (t₀, c₀)))
    (A : LExponentialGeometry F t₀.val τmax c₀) {τ : ℝ}
    (hτ : 0 < τ) (hmax : τ < τmax)
    (Z : G.Horizontal (e.toSpacetime (t₀, c₀)))
    (hstable : M14StableInitialVector G t₀.val τ (e.toSpacetime (t₀, c₀)) E Z) :
    ((g.spatialTangentEquiv t₀ c₀).symm Z, τ) ∈ A.toLExponentialFamily.regularDomain := by
  obtain ⟨hZD, hbij, N, hN, hZN, huniq⟩ := hstable
  let L := g.spatialTangentEquiv t₀ c₀
  let W := L.symm Z
  let U := L ⁻¹' N
  have hU : IsOpen U := hN.preimage L.continuous
  have hWU : W ∈ U := by simpa only [U, W, mem_preimage, L.apply_symm_apply] using hZN
  have htransport (V : TangentSpace (𝓡 n) c₀) (hV : V ∈ U) :=
    ordinaryCapture_unique_branch_transport t₀ c₀ D hCoordinates hPath E A hτ hmax
      (L V) (huniq (L V) hV)
  have hsurv (V : TangentSpace (𝓡 n) c₀) (hV : V ∈ U) : (L V, Real.sqrt τ) ∈ E.domain :=
    (huniq (L V) hV).1
  have hvalid := (A.path W τ hτ hmax).time_mem τ ⟨hτ.le, le_rfl⟩
  have heq (V : TangentSpace (𝓡 n) c₀) (hV : V ∈ U) :
      E.gamma (L V) (Real.sqrt τ) = e.toSpacetime (⟨t₀.val - τ, hvalid⟩, A.gamma V τ) := by
    have hr := ordinaryCapture_point_reconstruct D (htransport V hV).2.1
      ⟨t₀.val - τ, hvalid⟩
      (by simpa only [Real.sq_sqrt hτ.le] using E.clock _ _ (hsurv V hV))
    rw [(htransport V hV).2.2, ContinuousLinearEquiv.symm_apply_apply] at hr
    exact hr.symm
  have hW : (g.spatialTangentEquiv t₀ c₀ W, Real.sqrt τ) ∈ E.domain := by
    simpa only [W, L, ContinuousLinearEquiv.apply_symm_apply] using hZD
  have hb : Function.Bijective
      (E.differential (g.spatialTangentEquiv t₀ c₀ W) (Real.sqrt τ) hW) := by
    have h (Y : G.Horizontal (e.toSpacetime (t₀, c₀))) (hY : Y = Z)
        (hYD : (Y, Real.sqrt τ) ∈ E.domain) :
        Function.Bijective (E.differential Y (Real.sqrt τ) hYD) := by
      subst Y
      exact hbij
    exact h _ (L.apply_symm_apply Z) hW
  have hd := (ordinaryCapture_differential_bijective_iff t₀ c₀ D hCoordinates E
    A.toLExponentialFamily hτ hmax hvalid W hW U hU hWU hsurv heq).mp hb
  refine ⟨?_, hd⟩
  simpa only [L, W, ContinuousLinearEquiv.apply_symm_apply] using (htransport W hWU).1

end PoincareConjecture.M14
