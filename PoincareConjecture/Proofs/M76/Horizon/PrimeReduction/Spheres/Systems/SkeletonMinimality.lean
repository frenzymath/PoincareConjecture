import PoincareConjecture.Proofs.M76.PrimeReduction.SphereAmbientTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.OriginalSkeletonContactCount
import Mathlib.Data.Nat.Find

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_sphere_system_skeleton_minimum
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X)
    {Z : Set X} (hSZ : Disjoint (⋃ i, S i) Z)
    (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (S i) K g a) :
    ∃ (F : X ≃ₜ X) (W : Set X),
      Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) ∧
      IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧ EqOn F id W ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (Pairwise fun i j => Disjoint (F '' S i) (F '' S j)) ∧
      Disjoint (F '' (⋃ i, S i)) Z ∧
      Disjoint (F '' (⋃ i, S i)) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i, ∀ a ∈ K.faces, a.card = 2 →
        HasOriginalEdgeCofaceCharts e (F '' S i) K g a) ∧
      (((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).Finite) ∧
      ∀ (G : X ≃ₜ X) (V : Set X),
        IsOpen V → Z ∪ g '' K.vertices ⊆ V → EqOn G id V →
        (∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) →
        (∀ i j, (e i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) →
        (∀ a ∈ K.faces, a.card = 2 →
          ((G '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) →
        (∀ i, ∀ a ∈ K.faces, a.card = 2 →
          HasOriginalEdgeCofaceCharts e (G '' S i) K g a) →
        ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
          (F '' (⋃ i, S i))).ncard ≤
        ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
          (G '' (⋃ i, S i))).ncard := by
  classical
  let admissible (F : X ≃ₜ X) : Prop :=
    (∃ W : Set X, IsOpen W ∧ Z ∪ g '' K.vertices ⊆ W ∧ EqOn F id W) ∧
    (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) ∧
    (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) ∧
    (∀ a ∈ K.faces, a.card = 2 →
      ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
    (∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (F '' S i) K g a)
  let count (F : X ≃ₜ X) : ℕ :=
    ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
      (F '' (⋃ i, S i))).ncard
  have hid : ∀ i j, (e i).symm.trans
      ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 := by
    intro i j
    change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
    simpa only [OpenPartialHomeomorph.refl_trans] using he i j
  have hidentity : admissible (Homeomorph.refl X) := by
    refine ⟨⟨univ, isOpen_univ, subset_univ _, fun _ _ => rfl⟩, hid, hid, ?_, ?_⟩
    · simpa only [Homeomorph.refl_apply, id_eq, image_id'] using hedges
    · simpa only [Homeomorph.refl_apply, id_eq, image_id'] using hcofaces
  have hex : ∃ n : ℕ, ∃ F : X ≃ₜ X, admissible F ∧ count F = n :=
    ⟨count (Homeomorph.refl X), Homeomorph.refl X, hidentity, rfl⟩
  obtain ⟨F, hF, hcount⟩ := Nat.find_spec hex
  obtain ⟨⟨W, hW, hmarks, hfix⟩, hFPL, hFinv, hFedges, hFcofaces⟩ := hF
  have hsF : Nonempty (∀ i, ChartwisePLSphere e (F '' S i)) :=
    ⟨fun i => Classical.choice ((sS i).nonempty_image F hcover hFPL)⟩
  have hdisF : Pairwise fun i j => Disjoint (F '' S i) (F '' S j) := by
    intro i j hij
    exact (hdis hij).image F.injective.injOn (subset_univ _) (subset_univ _)
  have hprotected : Disjoint (F '' (⋃ i, S i)) (Z ∪ g '' K.vertices) := by
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ hxmark
    have hyx' : y = x := F.injective (hyx.trans (hfix (hmarks hxmark)).symm)
    exact disjoint_left.mp (disjoint_union_right.mpr ⟨hSZ, hSV⟩) (hyx' ▸ hy) hxmark
  have hcontactFinite :
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).Finite := by
    let := K.finite_faceOfCard hK 2
    rw [iUnion_inter]
    apply Set.finite_iUnion
    intro a
    simpa only [inter_comm] using hFedges a.1 a.2.1 a.2.2
  refine ⟨F, W, hsF, hW, hmarks, hfix, hFPL, hFinv, hdisF,
    hprotected.mono_right subset_union_left, hprotected.mono_right subset_union_right,
    hFedges, hFcofaces, hcontactFinite, ?_⟩
  intro G V hV hmarksG hfixG hGPL hGinv hGedges hGcofaces
  have hG : admissible G :=
    ⟨⟨V, hV, hmarksG, hfixG⟩, hGPL, hGinv, hGedges, hGcofaces⟩
  change count F ≤ count G
  rw [hcount]
  exact Nat.find_min' hex ⟨G, hG, rfl⟩

end PoincareConjecture.M76
