import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SkeletonMinimality
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.AmbientTransport









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

def IsProtectedSkeletonMinimum
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (S : κ → Set X)
    (K : SimplicialComplex ℝ E) (g : E → X) (Z : Set X) : Prop :=
  ∀ (F : X ≃ₜ X) (W : Set X),
    IsOpen W → Z ∪ g '' K.vertices ⊆ W → EqOn F id W →
    (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) →
    (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) →
    (∀ a ∈ K.faces, a.card = 2 →
      ((F '' (⋃ i, S i)) ∩ (g '' convexHull ℝ (a : Set E))).Finite) →
    (∀ i, ∀ a ∈ K.faces, a.card = 2 →
      HasOriginalEdgeCofaceCharts e (F '' S i) K g a) →
    ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard ≤
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
        (F '' (⋃ i, S i))).ncard

theorem protected_skeleton_minimum_of_attained_orbit_minimum
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} (S : κ → Set X)
    (K : SimplicialComplex ℝ E) (g : E → X) (Z : Set X)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X) {W : Set X} (hW : IsOpen W)
    (hmarks : Z ∪ g '' K.vertices ⊆ W) (hfix : EqOn F id W)
    (hFPL : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hmin : ∀ (G : X ≃ₜ X) (V : Set X),
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
        (G '' (⋃ i, S i))).ncard) :
    IsProtectedSkeletonMinimum e (fun i => F '' S i) K g Z := by
  intro G V hV hmarksG hfixG hGPL hGinv hGedges hGcofaces
  have himage (B : Set X) : (F.trans G) '' B = G '' (F '' B) := by
    rw [image_image]
    rfl
  obtain ⟨hPL, hinv⟩ := original_PL_motion_trans_both e hcover F G hFPL hFinv hGPL hGinv
  obtain ⟨hWV, hmarksWV, hfixWV, _⟩ := protected_ambient_trans_neighborhood
    F G hW hV hmarks hmarksG hfix hfixG
  have h := hmin (F.trans G) (W ∩ V) hWV hmarksWV hfixWV hPL hinv
    (by simpa only [himage, image_iUnion] using hGedges)
    (by simpa only [himage] using hGcofaces)
  simpa only [himage, image_iUnion] using h

theorem IsProtectedSkeletonMinimum.image_of_same_count
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : κ → Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {Z : Set X}
    (hmin : IsProtectedSkeletonMinimum e S K g Z)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X) {W : Set X} (hW : IsOpen W)
    (hmarks : Z ∪ g '' K.vertices ⊆ W) (hfix : EqOn F id W)
    (hFPL : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hcount : ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
      (F '' (⋃ i, S i))).ncard =
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ (⋃ i, S i)).ncard) :
    IsProtectedSkeletonMinimum e (fun i => F '' S i) K g Z := by
  apply protected_skeleton_minimum_of_attained_orbit_minimum S K g Z hcover F
    hW hmarks hfix hFPL hFinv
  intro G V hV hmarksG hfixG hGPL hGinv hGedges hGcofaces
  rw [hcount]
  exact hmin G V hV hmarksG hfixG hGPL hGinv hGedges hGcofaces

end PoincareConjecture.M76
