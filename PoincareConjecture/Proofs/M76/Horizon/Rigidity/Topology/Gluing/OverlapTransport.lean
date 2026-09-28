import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.FamilyRegularActions
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.ComponentMapTransport

set_option autoImplicit false

open scoped unitInterval

namespace PoincareConjecture.M76.IncompressibleGluing

universe u

variable {G J : Type u} [Group G] [Group J]

def regularSecond (G J : Type u) [Group G] [Group J] :
    J →* Equiv.Perm (G × J) :=
  (Equiv.prodComm J G).permCongrHom.toMonoidHom.comp (regularProduct J G)

private theorem mulSingle_mul {Index : Type u} {F : Index → Type u} [∀ i, Group (F i)]
    [DecidableEq Index] (i : Index) (g : F i) (p : ∀ j, F j) :
    Pi.mulSingle i g * p = Function.update p i (g * p i) := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]

open Classical in
private theorem exists_component_exchange
    {W U V : Type u} [TopologicalSpace W] [TopologicalSpace U] [TopologicalSpace V]
    (f : C(W, U)) (g : C(W, V)) (c : ZerothHomotopy W)
    (hf : Function.Injective (FundamentalGroup.map f c.out))
    (hg : Function.Injective (FundamentalGroup.map g c.out)) :
    ∃ e : Equiv.Perm ((∀ i, ComponentGroup U i) × (∀ j, ComponentGroup V j)),
      ∀ q : ComponentGroup W c,
        e * regularProduct _ (∀ j, ComponentGroup V j)
            (Pi.mulSingle (imageComponent f c) (componentMapHom f c q)) =
          regularSecond (∀ i, ComponentGroup U i) _
            (Pi.mulSingle (imageComponent g c) (componentMapHom g c q)) * e := by
  obtain ⟨e, he⟩ := exists_family_regular_action_exchange
    (ComponentGroup U) (ComponentGroup V) (imageComponent f c) (imageComponent g c)
    (componentMapHom f c) (componentMapHom g c)
    (componentMapHom_injective f c hf) (componentMapHom_injective g c hg)
  refine ⟨e, ?_⟩
  intro q
  apply Equiv.ext
  intro p
  change e (Pi.mulSingle (imageComponent f c) (componentMapHom f c q) * p.1, p.2) =
    ((e p).1, Pi.mulSingle (imageComponent g c) (componentMapHom g c q) * (e p).2)
  simpa only [mulSingle_mul] using he q p

variable {W U V : Type u} [TopologicalSpace W] [TopologicalSpace U] [TopologicalSpace V]

set_option backward.isDefEq.respectTransparency false in

theorem exists_overlap_transport_frame
    (f : C(W, U)) (g : C(W, V))
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x))
    (hg : ∀ x, Function.Injective (FundamentalGroup.map g x)) :
    ∃ frame : W → Equiv.Perm ((∀ i, ComponentGroup U i) × (∀ j, ComponentGroup V j)),
      ∀ p : C(unitInterval, W),
        regularProduct _ (∀ j, ComponentGroup V j) (componentTransport (f.comp p)) =
          frame (p 0) *
            regularSecond (∀ i, ComponentGroup U i) _ (componentTransport (g.comp p)) *
              (frame (p 1))⁻¹ := by
  classical
  let GU := ∀ i, ComponentGroup U i
  let GV := ∀ j, ComponentGroup V j
  let A := Equiv.Perm (GU × GV)
  let a : GU →* A := regularProduct GU GV
  let b : GV →* A := regularSecond GU GV
  choose e he using fun c : ZerothHomotopy W =>
    exists_component_exchange f g c (hf c.out) (hg c.out)
  let u (c : ZerothHomotopy W) (x : W) (hx : Joined c.out x) : A :=
    a (Pi.mulSingle (imageComponent f c) (componentMapGauge f c x hx))
  let v (c : ZerothHomotopy W) (x : W) (hx : Joined c.out x) : A :=
    b (Pi.mulSingle (imageComponent g c) (componentMapGauge g c x hx))
  let frameAt (c : ZerothHomotopy W) (x : W) (hx : Joined c.out x) : A :=
    u c x hx * (e c)⁻¹ * (v c x hx)⁻¹
  let frame (x : W) : A :=
    frameAt (ZerothHomotopy.mk x) x ((joined_component_out_iff _ _).mpr rfl)
  refine ⟨frame, ?_⟩
  intro p
  let c := ZerothHomotopy.mk (p 0)
  have h₀ : Joined c.out (p 0) := (joined_component_out_iff _ _).mpr rfl
  have h₁ : Joined c.out (p 1) := h₀.trans ⟨p.toPath⟩
  have hc₁ : ZerothHomotopy.mk (p 1) = c :=
    ((joined_component_out_iff _ _).mp h₁).symm
  have hframe₀ : frame (p 0) = frameAt c (p 0) h₀ := rfl
  have hframe₁ : frame (p 1) = frameAt c (p 1) h₁ := by
    dsimp only [frame]
    simp only [hc₁]
  let aq : A := a (Pi.mulSingle (imageComponent f c)
    (componentMapHom f c (componentTransport p c)))
  let bq : A := b (Pi.mulSingle (imageComponent g c)
    (componentMapHom g c (componentTransport p c)))
  have haq : aq = (e c)⁻¹ * bq * e c := by
    have h := he c (componentTransport p c)
    change e c * aq = bq * e c at h
    exact (eq_inv_mul_iff_mul_eq).mpr h |>.trans (mul_assoc _ _ _).symm
  have hfirst : a (componentTransport (f.comp p)) =
      u c (p 0) h₀ * aq * (u c (p 1) h₁)⁻¹ := by
    rw [componentTransport_map_eq_single f p c h₀ h₁]
    simp only [Pi.mulSingle_mul, Pi.mulSingle_inv, map_mul]
    dsimp only [u, aq]
    congr 1
    exact map_inv a _
  have hsecond : b (componentTransport (g.comp p)) =
      v c (p 0) h₀ * bq * (v c (p 1) h₁)⁻¹ := by
    rw [componentTransport_map_eq_single g p c h₀ h₁]
    simp only [Pi.mulSingle_mul, Pi.mulSingle_inv, map_mul]
    dsimp only [v, bq]
    congr 1
    exact map_inv b _
  change a (componentTransport (f.comp p)) =
    frame (p 0) * b (componentTransport (g.comp p)) * (frame (p 1))⁻¹
  rw [hframe₀, hframe₁, hfirst, hsecond, haq]
  dsimp only [frameAt]
  simp only [mul_inv_rev, mul_assoc]
  simp only [A, inv_inv, inv_mul_cancel_left]

end PoincareConjecture.M76.IncompressibleGluing
