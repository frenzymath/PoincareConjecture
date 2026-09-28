import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalDiskReplacement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

open Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def capSpoke (x : E) : ℝ →ᴬ[ℝ] E × ℝ :=
  ContinuousAffineMap.lineMap (0, 1) (x, 0)

@[simp] theorem capSpoke_apply (x : E) (t : ℝ) :
    capSpoke x t = (t • x, 1 - t) := by
  simp [capSpoke, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module,
    Prod.smul_mk, Prod.mk_add_mk]

theorem capSpoke_mem {q : Set E} {x : E} (hx : x ∈ q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : capSpoke x t ∈ boundaryCircleCap true q := by
  exact (mem_boundaryCircleCap_iff true q _).mpr ⟨x, hx, t, ht, by simp [capSign]⟩

theorem capSpoke_fibers (x y : E) (u v : ℝ) :
    capSpoke x u = capSpoke y v ↔ u = v ∧ (u = 0 ∨ x = y) := by
  rw [capSpoke_apply, capSpoke_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨hxy, huv⟩
    have huv' : u = v := by linarith
    refine ⟨huv', ?_⟩
    by_cases hu : u = 0
    · exact Or.inl hu
    · right
      rw [← huv'] at hxy
      exact (smul_right_injective E hu) hxy
  · rintro ⟨rfl, h | rfl⟩
    · simp [h]
    · exact ⟨rfl, rfl⟩

theorem capSpoke_finitePL (x : E) :
    FinitePiecewiseAffineOn (capSpoke x) (Icc (0 : ℝ) 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  exact ⟨J, hJ, hJs, J.affineOnFaces_affine (capSpoke x)⟩

variable [FiniteDimensional ℝ E]

theorem exists_primal_disk_spokes {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (x₀ : q) :
    ∃ center ∈ d \ q, ∃ f : q → ℝ → E,
      (∀ x, FinitePiecewiseAffineOn (f x) (Icc (0 : ℝ) 1)) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) 1 → f x t ∈ d) ∧
      (∀ x, f x 0 = center ∧ f x 1 = (x : E)) ∧
      (∀ x y u v, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
        (f x u = f y v ↔ u = v ∧ (u = 0 ∨ x = y))) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) 1 → (f x t ∈ q ↔ t = 1)) := by
  obtain ⟨H, hH, hHb, hHrim⟩ := exists_disk_cap_homeomorph hd
  obtain ⟨g, hg, hgval⟩ := hH.symm
  let f : q → ℝ → E := fun x ↦ g ∘ capSpoke (x : E)
  have hmem (x : q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      capSpoke (x : E) t ∈ boundaryCircleCap true q := capSpoke_mem x.property ht
  have hfval (x : q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f x t = (H.symm ⟨capSpoke (x : E) t, hmem x t ht⟩ : E) :=
    (hgval ⟨capSpoke (x : E) t, hmem x t ht⟩).symm
  have hfmem (x : q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f x t ∈ d := by
    rw [hfval x t ht]
    exact (H.symm _).property
  have hforward (x : q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (H ⟨f x t, hfmem x t ht⟩ : E × ℝ) = capSpoke (x : E) t := by
    have he : (⟨f x t, hfmem x t ht⟩ : d) =
        H.symm ⟨capSpoke (x : E) t, hmem x t ht⟩ := Subtype.ext (hfval x t ht)
    rw [he, H.apply_symm_apply]
  have hfrim (x : q) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f x t ∈ q ↔ t = 1 := by
    rw [hHrim ⟨f x t, hfmem x t ht⟩, hforward x t ht, capSpoke_apply]
    constructor
    · intro h
      have : 1 - t = 0 := h.2
      linarith
    · rintro rfl
      simp
  refine ⟨g (0, 1), ⟨?_, ?_⟩, f, ?_, hfmem, ?_, ?_, hfrim⟩
  · simpa [f] using hfmem x₀ 0 (by constructor <;> norm_num)
  · intro h
    have : f x₀ 0 ∈ q := by simpa [f] using h
    have := (hfrim x₀ 0 (by constructor <;> norm_num)).mp this
    norm_num at this
  · intro x
    exact hg.comp (capSpoke_finitePL (x : E)) (fun t ht ↦ hmem x t ht)
  · intro x
    refine ⟨by simp [f], ?_⟩
    have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
    apply congrArg Subtype.val (H.injective (a₁ := ⟨f x 1, hfmem x 1 ht⟩)
      (a₂ := ⟨x, hd.1 x.property⟩) ?_)
    apply Subtype.ext
    rw [hforward x 1 ht, hHb x]
    simp
  · intro x y u v hu hv
    have heq : f x u = f y v ↔ capSpoke (x : E) u = capSpoke (y : E) v := by
      constructor
      · intro h
        rw [← hforward x u hu, ← hforward y v hv]
        exact congrArg (fun z : d ↦ (H z : E × ℝ)) (Subtype.ext h)
      · intro h
        exact congrArg g h
    rw [heq, capSpoke_fibers]
    exact and_congr_right fun _ ↦ or_congr_right Subtype.val_inj

end PoincareConjecture.M76.OriginalTriangleCopies
