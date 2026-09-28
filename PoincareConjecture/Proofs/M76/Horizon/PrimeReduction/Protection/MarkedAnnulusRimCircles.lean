import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedProductCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SquareCircle

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

theorem exists_unit_sphere_circle_homeomorph
    {ι : Type*} [Fintype ι] (hdim : Fintype.card ι = 2) :
    Nonempty (sphere (0 : ι → ℝ) 1 ≃ₜ Circle) := by
  classical
  let tau : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hdim
  let E : (ι → ℝ) ≃ᵢ (Fin 2 → ℝ) := IsometryEquiv.piCongrLeft' tau
  have hnorm (x : ι → ℝ) : ‖E x‖ = ‖x‖ := by
    simpa only [show E 0 = 0 from rfl, dist_zero_right] using E.isometry.dist_eq x 0
  let e : sphere (0 : ι → ℝ) 1 ≃ₜ sphere (0 : Fin 2 → ℝ) 1 :=
    E.toHomeomorph.subtype (fun x => by
      change x ∈ sphere 0 1 ↔ E x ∈ sphere 0 1
      simp only [mem_sphere_zero_iff_norm, hnorm])
  obtain ⟨j,_,_,_,_⟩ := Dehn.exists_square_circle_coordinates
  exact ⟨(e.trans j.symm).trans (AddCircle.homeomorphCircle (by norm_num))⟩

theorem exists_marked_annulus_rim_circles
    {ι κ E : Type*} [Fintype ι] [Fintype κ] [Unique κ]
    [TopologicalSpace E] [T2Space E] {T : Set E}
    (hdim : Fintype.card ι = 2)
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ T) :
    ∃ (S : Bool → Set E) (_H : ∀ b, S b ≃ₜ Circle),
      (∀ b, S b = range (fun x : sphere (0 : ι → ℝ) 1 =>
        (P ⟨((x : ι → ℝ),fun _ => if b then (3 / 2 : ℝ) else -(3 / 2 : ℝ)),
          x.property, by
            rw [mem_closedBall_zero_iff,pi_norm_const,Real.norm_eq_abs]
            cases b <;> norm_num⟩ : E))) ∧
      Pairwise (fun b c => Disjoint (S b) (S c)) ∧
      (⋃ b, S b) = (Subtype.val : T → E) ''
        (P '' {x | (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2)}) := by
  classical
  let endpoint (b : Bool) : κ → ℝ := fun _ => if b then 3 / 2 else -(3 / 2 : ℝ)
  have hend (b : Bool) : endpoint b ∈ sphere (0 : κ → ℝ) (3 / 2) := by
    rw [mem_sphere_zero_iff_norm,pi_norm_const,Real.norm_eq_abs]
    cases b <;> norm_num
  let f (b : Bool) (x : sphere (0 : ι → ℝ) 1) : E :=
    P ⟨((x : ι → ℝ),endpoint b),x.property,sphere_subset_closedBall (hend b)⟩
  have hf (b : Bool) : Continuous (f b) := by
    exact continuous_subtype_val.comp (P.continuous.comp
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _))
  have hfi (b : Bool) : Function.Injective (f b) := by
    intro x y h
    have hxy := congrArg Subtype.val (P.injective (Subtype.ext h))
    exact Subtype.ext (congrArg Prod.fst hxy)
  obtain ⟨g⟩ := exists_unit_sphere_circle_homeomorph hdim
  let e (b : Bool) : sphere (0 : ι → ℝ) 1 ≃ₜ range (f b) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective (f b) (hfi b))
      ((hf b).subtype_mk _)
  refine ⟨fun b => range (f b),fun b => (e b).symm.trans g,fun _ => rfl,?_,?_⟩
  · intro b c hbc
    apply disjoint_left.mpr
    rintro y ⟨x,hx⟩ ⟨z,hz⟩
    have heq := congrArg (fun t => t.val.2 default)
      (P.injective (Subtype.ext (hx.trans hz.symm)))
    cases b <;> cases c <;> norm_num [endpoint] at *
  · ext y
    constructor
    · intro hy
      obtain ⟨b,hb⟩ := mem_iUnion.mp hy
      obtain ⟨x,rfl⟩ := hb
      exact ⟨_,⟨⟨((x : ι → ℝ),endpoint b),x.property,sphere_subset_closedBall (hend b)⟩,
        hend b,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      have hconst : x.val.2 = fun _ => x.val.2 default := by
        funext k
        exact congrArg x.val.2 (Subsingleton.elim k default)
      have habs : |x.val.2 default| = (3 / 2 : ℝ) := by
        have hh := mem_sphere_zero_iff_norm.mp hx
        rw [hconst,pi_norm_const,Real.norm_eq_abs] at hh
        exact hh
      have he : ∃ b, x.val.2 = endpoint b := by
        rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 3 / 2)).mp habs with h | h
        · exact ⟨true,hconst.trans (by simp [endpoint,h])⟩
        · exact ⟨false,hconst.trans (by simp [endpoint,h])⟩
      obtain ⟨b,hb⟩ := he
      apply mem_iUnion.mpr
      refine ⟨b,⟨⟨x.val.1,x.property.1⟩,?_⟩⟩
      apply congrArg (fun z => (P z : E))
      exact Subtype.ext (Prod.ext rfl hb.symm)

end PoincareConjecture.M76
