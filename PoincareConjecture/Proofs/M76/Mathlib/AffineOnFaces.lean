import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def AffineOnFaces (K : SimplicialComplex ℝ E) (f : E → F) : Prop :=
  ∀ s ∈ K.faces, ∃ a : E →ᴬ[ℝ] F, EqOn f a (convexHull ℝ (s : Set E))

variable {K L : SimplicialComplex ℝ E} {f g : E → F}

theorem affineOnFaces_affine (K : SimplicialComplex ℝ E) (a : E →ᴬ[ℝ] F) :
    K.AffineOnFaces a :=
  fun _ _ => ⟨a, fun _ _ => rfl⟩

theorem AffineOnFaces.congr (hf : K.AffineOnFaces f) (hfg : EqOn f g K.space) :
    K.AffineOnFaces g := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  exact ⟨a, fun _ hx => (hfg (convexHull_subset_space hs hx)).symm.trans (ha hx)⟩

theorem AffineOnFaces.of_face_containment (hf : K.AffineOnFaces f)
    (hLK : ∀ s ∈ L.faces, ∃ t ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) : L.AffineOnFaces f := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  obtain ⟨a, ha⟩ := hf t ht
  exact ⟨a, fun _ hx => ha (hst hx)⟩

theorem AffineOnFaces.postcomp (hf : K.AffineOnFaces f) (b : F →ᴬ[ℝ] G) :
    K.AffineOnFaces (b ∘ f) := by
  intro s hs
  obtain ⟨a, ha⟩ := hf s hs
  exact ⟨b.comp a, fun _ hx => congrArg b (ha hx)⟩

theorem AffineOnFaces.continuousOn_of_locallyFinite (hf : K.AffineOnFaces f)
    (hlocal : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E))) :
    ContinuousOn f K.space := by
  have hcont : ContinuousOn f (⋃ s : K.faces, convexHull ℝ (s.val : Set E)) := by
    apply hlocal.continuousOn_iUnion
    · intro s
      exact s.val.finite_toSet.isClosed_convexHull ℝ
    · intro s
      obtain ⟨a, ha⟩ := hf s.val s.property
      exact a.continuous.continuousOn.congr ha
  simpa only [space, iUnion_subtype] using hcont

theorem AffineOnFaces.continuousOn (hf : K.AffineOnFaces f) (hfinite : K.faces.Finite) :
    ContinuousOn f K.space := by
  let := hfinite.fintype
  exact hf.continuousOn_of_locallyFinite (locallyFinite_of_finite _)

end Geometry.SimplicialComplex
