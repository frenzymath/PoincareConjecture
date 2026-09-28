import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinalBallAnnulus

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "RimP" => sphere (0 : P2) 1
local notation "RimV" => sphere (0 : V2) 1

theorem exists_final_ball_marked_annular_collar_on_panel_rim
    {X : Type} [TopologicalSpace X] [T2Space X]
    {B : Set X} (H : (Disk ×ˢ I : Set (P2 × ℝ)) ≃ₜ B)
    {k : P2 × ℝ → X} {a₀ : P2 × ℝ → X}
    (hkv : ∀ p : (Disk ×ˢ I : Set (P2 × ℝ)), k p = (H p : X))
    (hann : EqOn k a₀ (RimP ×ˢ I))
    {φ : V2 ≃ₜ P2}
    (hφ : ∀ z : V2, z ∈ RimV ↔ φ z ∈ RimP)
    (hφsurj : ∀ z : (RimP : Set P2), ∃ v : (RimV : Set V2), φ v = z) :
    ∃ HB : ((Disk : Set P2) × I) ≃ₜ B,
      ∃ a : (RimV : Set V2) × I → X,
        ∃ q : (RimV : Set V2) → (Disk : Set P2),
          Function.Injective a ∧
          (∀ z t, (HB (q z, t) : X) = a (z, t)) ∧
          (∀ y t, (HB (y, t) : X) ∈ range a ↔ ∃ z, q z = y) ∧
          (∀ z t, a (z, t) = a₀ (φ z.1, t.1)) ∧
          (∀ z t, (HB (z, t) : X) = k (z.1, t.1)) := by
  obtain ⟨HB,aP,qP,haP,hparamP,hsideP,ha0P,hHB⟩ :=
    exists_final_ball_marked_annular_collar H hkv hann
  let rimMap (z : (RimV : Set V2)) : (RimP : Set P2) :=
    ⟨φ z.1,(hφ z.1).mp z.2⟩
  let a : (RimV : Set V2) × I → X := fun p => aP (rimMap p.1,p.2)
  let q : (RimV : Set V2) → (Disk : Set P2) := fun z => qP (rimMap z)
  have ha : Function.Injective a := by
    intro p p' hpp'
    change aP (rimMap p.1,p.2) = aP (rimMap p'.1,p'.2) at hpp'
    have hp : (rimMap p.1,p.2) = (rimMap p'.1,p'.2) :=
      haP hpp'
    have hp' := congrArg (fun z : (RimP : Set P2) × I =>
      ((z.1 : P2),(z.2 : ℝ))) hp
    have hz : φ p.1 = φ p'.1 := congrArg Prod.fst hp'
    have hfirst : p.1 = p'.1 := Subtype.ext (φ.injective hz)
    exact Prod.ext hfirst (Subtype.ext (congrArg Prod.snd hp'))
  have hparam : ∀ z t, (HB (q z,t) : X) = a (z,t) := by
    intro z t
    change (HB (qP (rimMap z),t) : X) = aP (rimMap z,t)
    exact hparamP (rimMap z) t
  have hside : ∀ y t, (HB (y,t) : X) ∈ range a ↔ ∃ z, q z = y := by
    intro y t
    constructor
    · rintro ⟨p,hp⟩
      obtain ⟨zp,hzp⟩ := (hsideP y t).mp ⟨(rimMap p.1,p.2),hp⟩
      obtain ⟨z,hz⟩ := hφsurj zp
      have hrim : rimMap z = zp := Subtype.ext hz
      exact ⟨z, by
        dsimp [q]
        rw [hrim,hzp]⟩
    · rintro ⟨z,hzy⟩
      refine ⟨(z,t), ?_⟩
      change a (z,t) = HB (y,t)
      rw [← hparam z t, hzy]
  refine ⟨HB,a,q,ha,hparam,hside,?_,hHB⟩
  intro z t
  exact ha0P (rimMap z) t

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
