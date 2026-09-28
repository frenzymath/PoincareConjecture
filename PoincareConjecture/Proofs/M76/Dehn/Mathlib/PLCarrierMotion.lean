import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import Mathlib.Topology.UnitInterval











set_option autoImplicit false

open Set unitInterval

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





structure PLCarrierMotion (C P : Set E) (ε : ℝ) where
  map : I → E ≃ₜ E
  continuous_map : Continuous (fun p : I × E => map p.1 p.2)
  continuous_symm : Continuous (fun p : I × E => (map p.1).symm p.2)
  zero : ∀ x, map 0 x = x
  outside : ∀ t x, x ∉ interior C → map t x = x
  fixed_protected : ∀ t x, x ∈ P → map t x = x
  carrier : ∀ t, map t '' C = C
  finitePL : ∀ t, ∃ e : C ≃ₜ C, e.IsFinitePL ∧ ∀ x : C, (e x : E) = map t x
  small : ∀ t x, dist (map t x) x < ε

namespace PLCarrierMotion



noncomputable def refl (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (P : Set E) {ε : ℝ} (hε : 0 < ε) : PLCarrierMotion J.space P ε where
  map _ := Homeomorph.refl E
  continuous_map := continuous_snd
  continuous_symm := continuous_snd
  zero _ := rfl
  outside _ _ _ := rfl
  fixed_protected _ _ _ := rfl
  carrier _ := by simp
  finitePL _ := by
    refine ⟨Homeomorph.refl J.space, ?_, fun _ => rfl⟩
    exact ⟨id, ⟨J, hJ, rfl, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,
      fun _ => rfl⟩
  small _ x := by
    change dist x x < ε
    simpa only [dist_self] using hε





noncomputable def trans [FiniteDimensional ℝ E]
    {C P : Set E} {ε δ : ℝ}
    (F : PLCarrierMotion C P ε) (G : PLCarrierMotion C P δ) :
    PLCarrierMotion C P (ε + δ) where
  map t := (F.map t).trans (G.map t)
  continuous_map := G.continuous_map.comp
    (continuous_fst.prodMk F.continuous_map)
  continuous_symm := F.continuous_symm.comp
    (continuous_fst.prodMk G.continuous_symm)
  zero x := by
    change G.map 0 (F.map 0 x) = x
    rw [F.zero, G.zero]
  outside t x hx := by
    change G.map t (F.map t x) = x
    rw [F.outside t x hx, G.outside t x hx]
  fixed_protected t x hx := by
    change G.map t (F.map t x) = x
    rw [F.fixed_protected t x hx, G.fixed_protected t x hx]
  carrier t := by
    change (G.map t ∘ F.map t) '' C = C
    calc
      (G.map t ∘ F.map t) '' C = G.map t '' (F.map t '' C) :=
        (image_image (G.map t) (F.map t) C).symm
      _ = C := by rw [F.carrier, G.carrier]
  finitePL t := by
    obtain ⟨e, he, hval⟩ := F.finitePL t
    obtain ⟨d, hd, hdval⟩ := G.finitePL t
    refine ⟨e.trans d, he.trans hd, ?_⟩
    intro x
    change (d (e x) : E) = G.map t (F.map t x)
    rw [hdval, hval]
  small t x := by
    change dist (G.map t (F.map t x)) x < ε + δ
    calc
      dist (G.map t (F.map t x)) x ≤
          dist (G.map t (F.map t x)) (F.map t x) + dist (F.map t x) x :=
        dist_triangle _ _ _
      _ < δ + ε := add_lt_add (G.small t (F.map t x)) (F.small t x)
      _ = ε + δ := add_comm _ _

end PLCarrierMotion

end Geometry
