import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferedCoordinateModulus
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferBalls
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

theorem exists_local_coordinate_modulus (P : M44CapPersistencePredecessors.{u})
    (m : ℕ) {K H r a b Z : ℝ} (hK : 0 < K) (hH : 0 < H) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 ≤ b) (hZ : 1 ≤ Z) :
    ∃ B L : ℝ, 1 ≤ B ∧ 0 ≤ L ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ {T : ℝ}, 0 < T → T ≤ H → ∀ (F : RicciFlow 3 M (Icc 0 T)),
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞,
      (∀ t ∈ Icc 0 T, ∀ x ∈ e.target, (F.connection t).curvatureTensorNorm x ≤ K) →
      (∀ j ≤ m, ∀ x ∈ e.target, (F.connection 0).curvatureDerivativeNorm j x ≤ K) →
      ∀ {V : Set (EuclideanSpace ℝ (Fin 3))}, IsOpen V → V ⊆ e.source →
      (∀ x ∈ V, IsCompact (closure ((F.metric 0).ball (e x) r))) →
      (∀ x ∈ V, closure ((F.metric 0).ball (e x) r) ⊆ e.target) →
      (∀ x ∈ V, ∀ v, a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients e x v v) →
      (∀ x ∈ V, ∀ v, (F.metric 0).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
      (∀ x ∈ V, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) x‖ ≤ Z) →
      ∀ j ≤ m, ∀ x ∈ V,
        (∀ t ∈ Icc 0 T,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
        (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ L * |t - s|) := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_buffered_coordinate_modulus P 3 m
    hK hH hr ha hb hZ
  refine ⟨B, L, hB, hL, ?_⟩
  intro M _ _ _ _ _ T hT hTH F e hcurv hinitial V hV hsub hcompact hinside
    hlower hupper hjets j hj x hx
  let U : Opens M := ⟨e.target, e.open_target⟩
  let p : U := ⟨e x, e.map_source (hsub hx)⟩
  let c := targetChart e p
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c V :=
    (contMDiffOn_targetChart e p).mono hsub
  have hi : ∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3) c y).IsInvertible := by
    intro y hy
    have hd := (targetPartialDiffeomorph e p).isLocalDiffeomorphAt
      (𝓡 3) (𝓡 3) ∞ (hsub hy)
    exact ⟨hd.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hcurv' : ∀ t ∈ Icc 0 T, ∀ y : U,
      ((physicalBufferFlow F e).connection t).curvatureTensorNorm y ≤ K := by
    intro t ht y
    rw [physicalBufferFlow_curvatureTensorNorm]
    exact hcurv t ht y.1 y.2
  have hinitial' : ∀ l ≤ m, ∀ y : U,
      ((physicalBufferFlow F e).connection 0).curvatureDerivativeNorm l y ≤ K := by
    intro l hl y
    rw [physicalBufferFlow_curvatureDerivativeNorm]
    exact hinitial l hl y.1 y.2
  have hcompact' : ∀ y ∈ V,
      IsCompact (closure (((physicalBufferFlow F e).metric 0).ball (c y) r)) := by
    intro y hy
    apply physicalBufferFlow_isCompact_closure_ball F e 0 (c y) r
    · simpa only [c, targetChart_val e p (hsub hy)] using hcompact y hy
    · simpa only [c, targetChart_val e p (hsub hy)] using hinside y hy
  have hresult := hbound U hT hTH (physicalBufferFlow F e) hcurv' hinitial'
    hV hc hi hcompact'
    (fun y hy v => by
      rw [physicalBufferFlow_pullbackCoefficients F e p 0 (hsub hy)]
      exact hlower y hy v)
    (fun y hy v => by
      rw [physicalBufferFlow_pullbackCoefficients F e p 0 (hsub hy)]
      exact hupper y hy v)
    (fun y hy l hl => by
      rw [physicalBufferFlow_pullbackJets F e p 0 l (hsub hy)]
      exact hjets y hy l hl) j hj x hx
  constructor
  · intro t ht
    simpa only [c, physicalBufferFlow_pullbackJets F e p t j (hsub hx)] using hresult.1 t ht
  · intro s hs t ht
    simpa only [c, physicalBufferFlow_pullbackJets F e p t j (hsub hx),
      physicalBufferFlow_pullbackJets F e p s j (hsub hx)] using hresult.2 s hs t ht

end PoincareConjecture.M44
