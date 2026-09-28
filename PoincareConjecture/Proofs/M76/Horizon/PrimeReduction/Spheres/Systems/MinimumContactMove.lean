import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MinimumAmbientOrbit
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OriginalSkeletonContactCount

set_option autoImplicit false

open Set Geometry
open scoped BigOperators

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem no_strict_protected_skeleton_contact_move
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : κ → Set X}
    {K : Geometry.SimplicialComplex ℝ E} [Fintype (K.FaceOfCard 2)]
    (g : E → X) (hgi : InjOn g K.space) (Z : Set X)
    (hmin : IsProtectedSkeletonMinimum e S K g Z)
    (F : X ≃ₜ X) (W : Set X)
    (hW : IsOpen W) (hmarks : Z ∪ g '' K.vertices ⊆ W)
    (hfix : EqOn F id W)
    (hFPL : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hnewfinite : ∀ a ∈ K.faces, a.card = 2 →
      ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hnewcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (F '' S i) K g a)
    (hSold : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hSnew : Disjoint (F '' (⋃ i, S i)) (g '' K.vertices))
    (holdfinite : ∀ a : K.FaceOfCard 2,
      ((g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).Finite)
    (hdrop :
      (∑ a : K.FaceOfCard 2,
        ((g '' convexHull ℝ (a.1 : Set E)) ∩ (F '' (⋃ i, S i))).ncard) =
        (∑ a : K.FaceOfCard 2,
          ((g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard) - 2)
    (hcount : 2 ≤ ∑ a : K.FaceOfCard 2,
      ((g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard) :
    False := by
  have hnewfinite' : ∀ a : K.FaceOfCard 2,
      ((g '' convexHull ℝ (a.1 : Set E)) ∩ (F '' (⋃ i, S i))).Finite := by
    intro a
    simpa only [inter_comm] using hnewfinite a.1 a.2.1 a.2.2
  have hle := hmin F W hW hmarks hfix hFPL hFinv
    hnewfinite hnewcofaces
  rw [ncard_original_skeleton_contacts_eq_sum K g hgi (⋃ i, S i)
      hSold holdfinite,
    ncard_original_skeleton_contacts_eq_sum K g hgi (F '' (⋃ i, S i))
      hSnew hnewfinite'] at hle
  rw [hdrop] at hle
  omega

theorem no_two_contact_union_decrease_at_protected_minimum
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : κ → Set X}
    {K : Geometry.SimplicialComplex ℝ E}
    (g : E → X) (Z : Set X)
    (hmin : IsProtectedSkeletonMinimum e S K g Z)
    (F : X ≃ₜ X) (W : Set X)
    (hW : IsOpen W) (hmarks : Z ∪ g '' K.vertices ⊆ W)
    (hfix : EqOn F id W)
    (hFPL : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hnewfinite : ∀ a ∈ K.faces, a.card = 2 →
      ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hnewcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (F '' S i) K g a)
    (hdrop :
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).ncard + 2 =
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (⋃ i, S i)).ncard) :
    False := by
  have hle := hmin F W hW hmarks hfix hFPL hFinv hnewfinite hnewcofaces
  omega

end PoincareConjecture.M76
