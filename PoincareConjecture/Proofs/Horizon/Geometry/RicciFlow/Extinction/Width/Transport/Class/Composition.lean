import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Regular
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Rebasing.HomotopyNaturality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareConjecture

variable {M N O : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
  [TopologicalSpace O] [ChartedSpace LoopAmbient O] [IsManifold (𝓡 3) ∞ O]

theorem m67_loop_postcomposition_apply {f : C(M, N)}
    (L : M59LoopPostcomposition f) (gamma : C1FreeLoopSpace (M := M))
    (z : LoopCircle) : L.map gamma z = f (gamma z) := by
  rw [← (L.map gamma).boundary, L.extension_agreement, gamma.boundary]

noncomputable def m67LoopPostcompositionId : M59LoopPostcomposition (ContinuousMap.id M) where
  map := ContinuousMap.id _
  extension_agreement := fun _ _ => rfl
  maps_constant := fun _ => rfl

noncomputable def m67LoopPostcompositionComp {f : C(M, N)} {g : C(N, O)}
    (L : M59LoopPostcomposition f) (K : M59LoopPostcomposition g) :
    M59LoopPostcomposition (g.comp f) where
  map := K.map.comp L.map
  extension_agreement := fun gamma z => by
    change (K.map (L.map gamma)).extension z = g (f (gamma.extension z))
    rw [K.extension_agreement, L.extension_agreement]
  maps_constant := fun x => by
    change K.map (L.map (constantC1Loop x)) = constantC1Loop (g (f x))
    rw [L.maps_constant, K.maps_constant]

theorem m67_alpha_transport_refl
    (B : M59HigherBasepointTransportService.{u}) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    M67AlphaTransport B x x (ContinuousMap.id M) alpha alpha := by
  refine ⟨m67LoopPostcompositionId, Path.refl x,
    ⟨Path.refl (constantC1Loop x), fun _ _ => rfl⟩, ?_⟩
  exact ((B.transport 2).map_refl _).trans (m67_homotopy_map_id alpha)



theorem m67_alpha_transport_trans
    (B : M59HigherBasepointTransportService.{u})
    {x : M} {y : N} {z : O} {f : C(M, N)} {g : C(N, O)}
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y)}
    {gamma : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := O)) (constantC1Loop z)}
    (h₁ : M67AlphaTransport B x y f alpha beta)
    (h₂ : M67AlphaTransport B y z g beta gamma) :
    M67AlphaTransport B x z (g.comp f) alpha gamma := by
  obtain ⟨L, p, lp, hbeta⟩ := h₁
  obtain ⟨K, q, lq, hgamma⟩ := h₂
  let r := p.map g.continuous
  let lr : Path (constantC1Loop (g (f x))) (constantC1Loop (g y)) :=
    (lp.loop.map K.map.continuous).cast
      (K.maps_constant (f x)).symm (K.maps_constant y).symm
  let lpr : M59ConstantLoopPath r :=
    { loop := lr
      pointwise := fun t c => by
        change K.map (lp.loop t) c = g (p t)
        rw [m67_loop_postcomposition_apply, lp.pointwise] }
  let lpq : M59ConstantLoopPath (r.trans q) :=
    { loop := lr.trans lq.loop
      pointwise := fun t c => by
        simp only [Path.trans_apply]
        split_ifs
        · exact lpr.pointwise _ c
        · exact lq.pointwise _ c }
  refine ⟨m67LoopPostcompositionComp L K, r.trans q, lpq, ?_⟩
  have hnat := m67_basepoint_transport_naturality B K.map lp.loop lr
    (K.maps_constant (f x)) (K.maps_constant y) (fun _ => rfl)
    (surgeryHomotopyMap (n := 2) L.map (L.map_based rfl) alpha)
  change M59HigherBasepointTransport.map (B.transport 2) (lr.trans lq.loop)
      (surgeryHomotopyMap (n := 2) (K.map.comp L.map)
        ((congrArg K.map (L.map_based rfl)).trans (K.maps_constant (f x))) alpha) = gamma
  refine ((B.transport 2 (X := C1FreeLoopSpace (M := O))).map_trans
    lr lq.loop _).trans ?_
  rw [← m67_homotopy_map_comp L.map K.map (L.map_based rfl) (K.maps_constant (f x))]
  exact (congrArg (M59HigherBasepointTransport.map (B.transport 2) lq.loop) hnat).trans
    ((congrArg (fun b => M59HigherBasepointTransport.map (B.transport 2) lq.loop
      (surgeryHomotopyMap (n := 2) K.map (K.maps_constant y) b)) hbeta).trans hgamma)

end PoincareConjecture
