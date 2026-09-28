import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.TransportGauge

set_option autoImplicit false

open Set
open scoped unitInterval

namespace PoincareConjecture.M76.IncompressibleGluing

open Path.Homotopic.Quotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def imageComponent (f : C(X, Y)) (c : ZerothHomotopy X) : ZerothHomotopy Y :=
  ZerothHomotopy.mk (f c.out)

theorem imageComponent_eq (f : C(X, Y)) (c : ZerothHomotopy X) (x : X)
    (hx : Joined c.out x) : imageComponent f c = ZerothHomotopy.mk (f x) :=
  Quotient.sound ⟨hx.somePath.map f.continuous⟩

noncomputable def imageComponentTail (f : C(X, Y)) (c : ZerothHomotopy X) :
    Path.Homotopic.Quotient (imageComponent f c).out (f c.out) :=
  componentTails (imageComponent f c) (f c.out)
    ((joined_component_out_iff _ _).mpr rfl)

noncomputable def componentMapHom (f : C(X, Y)) (c : ZerothHomotopy X) :
    ComponentGroup X c →* ComponentGroup Y (imageComponent f c) :=
  mappedLoopHom f c.out (imageComponentTail f c)

theorem componentMapHom_injective (f : C(X, Y)) (c : ZerothHomotopy X)
    (hf : Function.Injective (FundamentalGroup.map f c.out)) :
    Function.Injective (componentMapHom f c) :=
  mappedLoopHom_injective f c.out (imageComponentTail f c) hf

noncomputable def componentMapGauge (f : C(X, Y)) (c : ZerothHomotopy X)
    (x : X) (hx : Joined c.out x) : ComponentGroup Y (imageComponent f c) :=
  mappedTailDifference f (imageComponentTail f c) (componentTails c x hx)
    (componentTails (imageComponent f c) (f x)
      ((joined_component_out_iff _ _).mpr (imageComponent_eq f c x hx)))

theorem componentTransport_map_gauge (f : C(X, Y)) (p : C(unitInterval, X))
    (c : ZerothHomotopy X) (h₀ : Joined c.out (p 0)) (h₁ : Joined c.out (p 1)) :
    componentTransport (f.comp p) (imageComponent f c) *
        componentMapGauge f c (p 1) h₁ =
      componentMapGauge f c (p 0) h₀ *
        componentMapHom f c (componentTransport p c) := by
  have hY₀ := (joined_component_out_iff (imageComponent f c) (f (p 0))).mpr
    (imageComponent_eq f c (p 0) h₀)
  have hY₁ := (joined_component_out_iff (imageComponent f c) (f (p 1))).mpr
    (imageComponent_eq f c (p 1) h₁)
  unfold componentTransport basedContinuousTransport
  rw [basedTransport_of_joined _ _ _ hY₀ hY₁,
    basedTransport_of_joined _ _ _ h₀ h₁]
  exact mapped_transport_gauge f (imageComponentTail f c)
    (componentTails c (p 0) h₀) (componentTails c (p 1) h₁)
    (componentTails (imageComponent f c) (f (p 0)) hY₀)
    (componentTails (imageComponent f c) (f (p 1)) hY₁) (mk p.toPath)

open Classical in

theorem componentTransport_map_eq_single (f : C(X, Y)) (p : C(unitInterval, X))
    (c : ZerothHomotopy X) (h₀ : Joined c.out (p 0)) (h₁ : Joined c.out (p 1)) :
    componentTransport (f.comp p) =
      Pi.mulSingle (imageComponent f c)
        (componentMapGauge f c (p 0) h₀ * componentMapHom f c (componentTransport p c) *
          (componentMapGauge f c (p 1) h₁)⁻¹) := by
  funext d
  by_cases hd : d = imageComponent f c
  · subst d
    rw [Pi.mulSingle_eq_same]
    exact (eq_mul_inv_iff_mul_eq).mpr (componentTransport_map_gauge f p c h₀ h₁)
  · rw [Pi.mulSingle_eq_of_ne hd]
    apply componentTransport_eq_one_of_ne
    exact fun h => hd (h.trans (imageComponent_eq f c (p 0) h₀).symm)

end PoincareConjecture.M76.IncompressibleGluing
