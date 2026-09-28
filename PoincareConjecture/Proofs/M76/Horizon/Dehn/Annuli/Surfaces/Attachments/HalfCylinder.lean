import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Q ×ˢ I : Set (V2 × ℝ))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_cylinder_half {T : Set E} (c : Cyl ≃ₜ T) (hc : c.IsFinitePL)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ (S : Set E) (hST : S ⊆ T) (H : Cyl ≃ₜ S), H.IsFinitePL ∧
      (∀ x : Cyl, (c.symm ⟨H x, hST (H x).property⟩ : V2 × ℝ) =
        (x.val.1, σ * (x.val.2 + 1) / 2)) ∧
      (∀ x : Cyl, (c x : E) ∈ S ↔ 0 ≤ σ * x.val.2) ∧
      (∀ u : Q, (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
        c ⟨(u, 0), u.property, by norm_num, by norm_num⟩) ∧
      ∀ u : Q, (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
        c ⟨(u, σ), u.property, by rcases hσ with rfl | rfl <;> norm_num⟩ := by
  obtain ⟨F, hF, hFv⟩ := hc
  let a : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((σ / 2) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ (V2 × ℝ) (σ / 2))
  have hav (x : V2 × ℝ) : a x = (x.1, σ * (x.2 + 1) / 2) := by
    refine Prod.ext rfl ?_
    change σ / 2 * x.2 + σ / 2 = _
    ring
  have hamap : MapsTo a Cyl Cyl := by
    intro x hx
    rw [hav]
    refine ⟨hx.1, ?_⟩
    rcases hσ with rfl | rfl <;> constructor <;> linarith [hx.2.1, hx.2.2]
  have hai : Function.Injective a := by
    intro x y h
    rw [hav, hav] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine Prod.ext (show x.1 = y.1 from h1) ?_
    dsimp at h2
    rcases hσ with rfl | rfl <;> linarith
  obtain ⟨K, hK, hKs, hKF⟩ := hF
  have ha : FinitePiecewiseAffineOn a Cyl := ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  have hcomp : FinitePiecewiseAffineOn (F ∘ a) Cyl :=
    (show FinitePiecewiseAffineOn F Cyl from ⟨K, hK, hKs, hKF⟩).comp ha hamap
  have hcompv (x : Cyl) : F (a x) = (c ⟨a x, hamap x.property⟩ : E) :=
    (hFv ⟨a x, hamap x.property⟩).symm
  have hcompi : InjOn (F ∘ a) Cyl := by
    intro x hx y hy h
    apply hai
    have heq : c ⟨a x, hamap hx⟩ = c ⟨a y, hamap hy⟩ :=
      Subtype.ext ((hFv ⟨a x, hamap hx⟩).trans
        (h.trans (hFv ⟨a y, hamap hy⟩).symm))
    exact congrArg (fun z : Cyl ↦ z.val) (c.injective heq)
  obtain ⟨H, hH, hHv⟩ := hcomp.exists_homeomorph_image hcompi
  let S := (F ∘ a) '' Cyl
  have hST : S ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Function.comp_apply, hcompv ⟨x, hx⟩]
    exact (c _).property
  have hvalue (x : Cyl) : (H x : E) = c ⟨a x, hamap x.property⟩ :=
    (hHv x).trans (hcompv x)
  refine ⟨S, hST, H, hH, ?_, ?_, ?_, ?_⟩
  · intro x
    have heq : (⟨H x, hST (H x).property⟩ : T) = c ⟨a x, hamap x.property⟩ :=
      Subtype.ext (hvalue x)
    rw [heq, c.symm_apply_apply]
    exact hav x
  · intro x
    constructor
    · rintro ⟨y, hy, heq⟩
      have hax : a y = x := congrArg (fun z : Cyl ↦ z.val) (c.injective
        (Subtype.ext ((hFv ⟨a y, hamap hy⟩).trans heq)))
      have hh := congrArg Prod.snd hax
      rw [hav] at hh
      dsimp at hh
      rcases hσ with rfl | rfl <;> nlinarith [hy.2.1]
    · intro hx
      let y : V2 × ℝ := (x.val.1, 2 * σ * x.val.2 - 1)
      have hy : y ∈ Cyl := by
        refine ⟨x.property.1, ?_⟩
        dsimp [y]
        rcases hσ with rfl | rfl <;> constructor <;>
          linarith [x.property.2.1, x.property.2.2]
      have hay : a y = x := by
        rw [hav]
        refine Prod.ext ?_ ?_
        · rfl
        dsimp [y]
        rcases hσ with rfl | rfl <;> ring
      refine ⟨y, hy, ?_⟩
      change F (a y) = (c x : E)
      rw [hay]
      exact (hFv x).symm
  · intro u
    refine (hvalue _).trans (congrArg (fun x : Cyl ↦ (c x : E)) (Subtype.ext ?_))
    change a (u, -1) = ((u : V2), 0)
    rw [hav]
    simp
  · intro u
    refine (hvalue _).trans (congrArg (fun x : Cyl ↦ (c x : E)) (Subtype.ext ?_))
    change a (u, 1) = ((u : V2), σ)
    rw [hav]
    congr 1
    dsimp
    ring

end PoincareConjecture.M76.Dehn.Annuli
