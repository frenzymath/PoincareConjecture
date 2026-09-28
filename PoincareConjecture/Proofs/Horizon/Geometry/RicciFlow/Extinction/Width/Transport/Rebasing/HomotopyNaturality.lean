import PoincareConjecture.Definitions.M59BasepointTransport

set_option autoImplicit false

open scoped Topology unitInterval

universe u v w

namespace PoincareConjecture

theorem m67_homotopy_map_comp
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {n : ℕ} {x : X} {y : Y} {z : Z}
    (f : C(X, Y)) (g : C(Y, Z)) (hf : f x = y) (hg : g y = z)
    (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap g hg (surgeryHomotopyMap f hf a) =
      surgeryHomotopyMap (g.comp f) ((congrArg g hf).trans hg) a := by
  induction a using Quotient.inductionOn with | h a => rfl

theorem m67_homotopy_map_id
    {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}
    (a : HomotopyGroup.Pi n X x) :
    surgeryHomotopyMap (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with | h a => rfl

theorem m67_basepoint_transport_naturality
    (B : M59HigherBasepointTransportService.{u})
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {x y : X} {x' y' : Y}
    (f : C(X, Y)) (p : Path x y) (q : Path x' y')
    (h₀ : f x = x') (h₁ : f y = y')
    (hq : ∀ t, q t = f (p t)) (a : HomotopyGroup.Pi n X x) :
    M59HigherBasepointTransport.map (B.transport n) q
        (surgeryHomotopyMap f h₀ a) =
      surgeryHomotopyMap f h₁
        (M59HigherBasepointTransport.map (B.transport n) p a) := by
  subst x'
  subst y'
  have hq' : q = p.map f.continuous := by ext t; exact hq t
  subst q
  exact B.naturality n f p a

private theorem cylinder_projection_injective
    {X : Type u} [TopologicalSpace X] {n : ℕ} (x : X) :
    Function.Injective (surgeryHomotopyMap (n := n) (x := (1, x)) (y := x)
      (⟨Prod.snd, continuous_snd⟩ : C(I × X, X))
      (rfl : ((1 : I), x).2 = x)) := by
  let section₁ : C(X, I × X) := ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  have hinverse (a : HomotopyGroup.Pi n (I × X) (1, x)) :
      surgeryHomotopyMap section₁ rfl
        (surgeryHomotopyMap (⟨Prod.snd, continuous_snd⟩ : C(I × X, X)) rfl a) = a := by
    induction a using Quotient.inductionOn with | h a =>
      apply Quotient.sound
      apply ContinuousMap.HomotopicRel.symm
      refine ⟨{ toFun := fun z => (max z.1 (a z.2).1, (a z.2).2)
                continuous_toFun := ?_
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · exact (continuous_fst.max (continuous_fst.comp
          (a.val.continuous.comp continuous_snd))).prodMk
          (continuous_snd.comp (a.val.continuous.comp continuous_snd))
      · intro z
        simp
      · intro z
        simp [section₁, surgeryMappedGenLoop, unitInterval.le_one']
      · intro t z hz
        change (max t (a z).1, (a z).2) = a z
        have haz : a z = (1, x) := a.property z hz
        rw [haz]
        simp [unitInterval.le_one']
  intro a b h
  rw [← hinverse a, ← hinverse b, h]

theorem m67_basepoint_transport_homotopy
    (B : M59HigherBasepointTransportService.{u})
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f g : C(X, Y)} (H : f.Homotopy g)
    (x : X) (a : HomotopyGroup.Pi n X x) :
    let p : Path (f x) (g x) :=
      { toFun := fun t => H (t, x)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := H.apply_zero x
        target' := H.apply_one x }
    M59HigherBasepointTransport.map (B.transport n) p
      (surgeryHomotopyMap f rfl a) = surgeryHomotopyMap g rfl a := by
  let i₀ : C(X, I × X) := ⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩
  let i₁ : C(X, I × X) := ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let r : C(I × X, X) := ⟨Prod.snd, continuous_snd⟩
  let p : Path ((0 : I), x) (1, x) :=
    { toFun := fun t => (t, x)
      continuous_toFun := continuous_id.prodMk continuous_const
      source' := rfl
      target' := rfl }
  have hproj (t : I) : r.comp (⟨fun z => (t, z),
      continuous_const.prodMk continuous_id⟩ : C(X, I × X)) = ContinuousMap.id X := rfl
  have hp : p.map r.continuous = Path.refl x := by ext t; rfl
  have hcyl : M59HigherBasepointTransport.map (B.transport n) p
      (surgeryHomotopyMap i₀ rfl a) = surgeryHomotopyMap i₁ rfl a := by
    apply cylinder_projection_injective x
    rw [← B.naturality n r p, hp]
    exact ((B.transport n (X := X)).map_refl _).trans (by
      simp only [m67_homotopy_map_comp]
      rfl)
  let q : Path (f x) (g x) :=
    { toFun := fun t => H (t, x)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := H.apply_zero x
      target' := H.apply_one x }
  have hnat := m67_basepoint_transport_naturality B H.toContinuousMap p q
    (H.apply_zero x) (H.apply_one x) (fun _ => rfl)
    (surgeryHomotopyMap i₀ rfl a)
  rw [hcyl] at hnat
  simp only [m67_homotopy_map_comp] at hnat
  have hf : H.toContinuousMap.comp i₀ = f := by ext z; exact H.apply_zero z
  have hg : H.toContinuousMap.comp i₁ = g := by ext z; exact H.apply_one z
  simp only [hf, hg] at hnat
  exact hnat

theorem m67_basepoint_transport_homotopy_between
    (B : M59HigherBasepointTransportService.{u})
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} {f g : C(X, Y)} (H : f.Homotopy g)
    (x : X) {y z : Y} (p : Path y z)
    (hy : f x = y) (hz : g x = z)
    (hp : ∀ t, H (t, x) = p t) (a : HomotopyGroup.Pi n X x) :
    M59HigherBasepointTransport.map (B.transport n) p
      (surgeryHomotopyMap f hy a) = surgeryHomotopyMap g hz a := by
  subst y
  subst z
  have h := m67_basepoint_transport_homotopy B H x a
  have hpath : (show Path (f x) (g x) from
      { toFun := fun t => H (t, x)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := H.apply_zero x
        target' := H.apply_one x }) = p := by ext t; exact hp t
  dsimp only at h
  subst p
  exact h

end PoincareConjecture
