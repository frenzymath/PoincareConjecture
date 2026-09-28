import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.Flags.EmbeddedThreeLocalFlags
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.GeometricFlags
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Flags.GeometricAffineFlags

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology.EmbeddedThreeFlagGrid

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {e : C(M, EuclideanSpace Real (Fin N))} {epsilon : NNReal}
  (G : EmbeddedThreeFlagGrid e epsilon)

def activeFaces : Set (Finset (EuclideanSpace Real (Fin N))) :=
  {s | s ∈ G.K.faces ∧ ∃ q : M,
    e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))}

instance activeFacesFintype : Fintype G.activeFaces :=
  (G.finite.subset (fun _ hs => hs.1)).fintype

def activeCenter (s : G.activeFaces) : EuclideanSpace Real (Fin N) :=
  finiteSectionCenter (Set.range e) (N - 2) s.val

theorem activeCenter_weights (s : G.activeFaces) :
    ∃ w : EuclideanSpace Real (Fin N) → Real,
      (∀ v ∈ s.val, 0 < w v) ∧ (∑ v ∈ s.val, w v) = 1 ∧
      (∑ v ∈ s.val, w v • v) = G.activeCenter s := by
  obtain ⟨_, w, hbound, hsum, hval⟩ := G.centers s s.property.1 s.property.2
  have heta : 0 < ambientGridGap N (N - 4) /
      (2 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) := by
    dsimp [ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  exact ⟨w, fun v hv => heta.trans_le (hbound v hv), hsum, hval⟩

theorem activeCenter_mem_hull (s : G.activeFaces) :
    G.activeCenter s ∈ convexHull Real (s.val : Set (EuclideanSpace Real (Fin N))) := by
  obtain ⟨w, hw, hsum, hval⟩ := G.activeCenter_weights s
  exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩

def activeFlagHomeomorph :
    (finiteOrderComplex G.activeFaces).space ≃ₜ
      Set.range (finiteOrderComplexMap G.activeFaces G.activeCenter) :=
  geometricFlagHomeomorphRange G.K Subtype.val (fun s => s.property.1)
    (fun _ _ => Iff.rfl) G.activeCenter G.activeCenter_weights

theorem activeFlag_injective :
    Function.Injective (finiteOrderComplexMap G.activeFaces G.activeCenter) := by
  intro x y h
  exact G.activeFlagHomeomorph.injective (Subtype.ext h)

theorem active_chain_card_le_four (t : Finset G.activeFaces)
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) : t.card ≤ 4 := by
  classical
  let rank (i : G.activeFaces) := i.val.card
  have hinj : Set.InjOn rank (t : Set G.activeFaces) := by
    intro i hi j hj hij
    rcases hchain i hi j hj with hle | hle
    · exact Subtype.ext (Finset.eq_of_subset_of_card_le hle (le_of_eq hij.symm))
    · exact (Subtype.ext (Finset.eq_of_subset_of_card_le hle (le_of_eq hij))).symm
  calc
    t.card = (t.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc (N - 2) (N + 1)).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr
        ⟨(G.centers i i.property.1 i.property.2).1, (G.geometry i i.property.1).1⟩
    _ ≤ 4 := by
      rw [Nat.card_Icc]
      have hN := G.ambient_dimension
      omega

theorem activeFlag_faces_card_le_four
    (t : Finset (G.activeFaces → Real)) (ht : t ∈ (finiteOrderComplex G.activeFaces).faces) :
    t.card ≤ 4 := by
  obtain ⟨s, _, hchain, rfl⟩ := (finiteOrderComplex_faces G.activeFaces t).mp ht
  exact (Finset.card_image_le).trans (G.active_chain_card_le_four s hchain)

def localFaces (p : M) : Set (Finset (EuclideanSpace Real (Fin N))) :=
  {s | s ∈ G.activeFaces ∧
    ∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
      ‖x - e p‖ ≤ 6 * (N + 1 : Real) * G.h}

instance localFacesFintype (p : M) : Fintype (G.localFaces p) :=
  (G.finite.subset (fun _ hs => hs.1.1)).fintype

def localTangentCenter (p : M) (s : G.localFaces p) : EuclideanSpace Real (Fin N) :=
  finiteSectionCenter {x | normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0}
    (N - 2) s.val

def localManifoldCenter (p : M) (s : G.localFaces p) : EuclideanSpace Real (Fin N) :=
  finiteSectionCenter (Set.range e) (N - 2) s.val

theorem localTangentCenter_spec (p : M) (s : G.localFaces p) :
    normalAffineConstraint (embeddedThreeTangent e p) (e p) (G.localTangentCenter p s) = 0 ∧
    (∃ w : EuclideanSpace Real (Fin N) → Real,
      (∀ v ∈ s.val, ambientGridGap N (N - 4) /
        (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) ≤ w v) ∧
      (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = G.localTangentCenter p s) ∧
    ‖G.localManifoldCenter p s - G.localTangentCenter p s‖ ≤
      24 * (N + 1 : Real) ^ 2 * (epsilon : Real) * G.h / ambientGridGap N (N - 4) :=
  (G.local_centers p s s.property.1.1 s.property.2).2 s.property.1.2

theorem localTangentCenter_weights (p : M) (s : G.localFaces p) :
    ∃ w : EuclideanSpace Real (Fin N) → Real,
      (∀ v ∈ s.val, 0 < w v) ∧ (∑ v ∈ s.val, w v) = 1 ∧
      (∑ v ∈ s.val, w v • v) = G.localTangentCenter p s := by
  obtain ⟨w, hbound, hsum, hval⟩ := (G.localTangentCenter_spec p s).2.1
  have heta : 0 < ambientGridGap N (N - 4) /
      (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) := by
    dsimp [ambientGridGap, ambientGridMoveRatio, ambientGridSlabRatio]
    positivity
  exact ⟨w, fun v hv => heta.trans_le (hbound v hv), hsum, hval⟩

def localTangentFlagHomeomorph (p : M) :
    (finiteOrderComplex (G.localFaces p)).space ≃ₜ
      Set.range (finiteOrderComplexMap (G.localFaces p) (G.localTangentCenter p)) :=
  geometricFlagHomeomorphRange G.K Subtype.val (fun s => s.property.1.1)
    (fun _ _ => Iff.rfl) (G.localTangentCenter p) (G.localTangentCenter_weights p)

theorem localTangentFlag_injective (p : M) :
    Function.Injective (finiteOrderComplexMap (G.localFaces p) (G.localTangentCenter p)) := by
  intro x y h
  exact (G.localTangentFlagHomeomorph p).injective (Subtype.ext h)

theorem localFaces_closed (p : M)
    (s : Finset (EuclideanSpace Real (Fin N))) (hs : s ∈ G.localFaces p)
    (t : Finset (EuclideanSpace Real (Fin N))) (hts : t ⊆ s)
    (ht : ∃ x ∈ convexHull Real (t : Set (EuclideanSpace Real (Fin N))),
      normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0) :
    t ∈ G.localFaces p := by
  have htne : t.Nonempty := by
    obtain ⟨x, hx, _⟩ := ht
    by_contra hn
    have ht0 := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [ht0, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hx
  have htK := G.K.down_closed hs.1.1 hts htne
  have hsize : ∀ x ∈ convexHull Real (t : Set (EuclideanSpace Real (Fin N))),
      ‖x - e p‖ ≤ 6 * (N + 1 : Real) * G.h :=
    fun x hx => hs.2 x (convexHull_mono hts hx)
  exact ⟨⟨htK, (G.local_centers p t htK hsize).1.mpr ht⟩, hsize⟩

theorem localTangentFlag_range (p : M) :
    Set.range (finiteOrderComplexMap (G.localFaces p) (G.localTangentCenter p)) =
      {x | ∃ s : G.localFaces p,
        x ∈ convexHull Real (s.val : Set (EuclideanSpace Real (Fin N))) ∧
          normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0} :=
  geometricAffineFlagMap_range (normalAffineConstraint (embeddedThreeTangent e p) (e p))
    (G.localFaces p) (G.localFaces_closed p) (G.localTangentCenter p)
    (fun s => ⟨(G.localTangentCenter_spec p s).1, G.localTangentCenter_weights p s⟩)

theorem localTangentFlag_covers_disk (p : M) (x : EuclideanSpace Real (Fin N))
    (hplane : normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0)
    (hsize : ‖x - e p‖ ≤ 4 * (N + 1 : Real) * G.h) :
    x ∈ Set.range (finiteOrderComplexMap (G.localFaces p) (G.localTangentCenter p)) := by
  have hLh : 0 < (N + 1 : Real) * G.h := mul_pos (by positivity) G.h_pos
  have hxspace : x ∈ G.K.space := by
    apply G.cover x
    have hdist : infDist x (Set.range e) ≤ ‖x - e p‖ := by
      exact (infDist_le_dist_of_mem (x := x) (Set.mem_range_self p)).trans_eq
        (dist_eq_norm x (e p))
    exact hdist.trans (hsize.trans (by nlinarith))
  obtain ⟨s, hsK, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxspace
  have hfaceSize : ∀ y ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
      ‖y - e p‖ ≤ 6 * (N + 1 : Real) * G.h := by
    intro y hy
    have hd : ‖y - x‖ ≤ 2 * (N + 1 : Real) * G.h := by
      rw [← dist_eq_norm]
      exact (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull Real).isBounded
        hy hxs).trans (G.geometry s hsK).2.1
    have htri := dist_triangle y x (e p)
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
    linarith
  have hsLocal : s ∈ G.localFaces p :=
    ⟨⟨hsK, (G.local_centers p s hsK hfaceSize).1.mpr ⟨x, hxs, hplane⟩⟩, hfaceSize⟩
  rw [G.localTangentFlag_range p]
  exact ⟨⟨s, hsLocal⟩, hxs, hplane⟩

theorem local_chain_card_le_four (p : M) (t : Finset (G.localFaces p))
    (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i) : t.card ≤ 4 := by
  classical
  let inc (s : G.localFaces p) : G.activeFaces := ⟨s.val, s.property.1⟩
  have hinj : Function.Injective inc := by
    intro i j hij
    exact Subtype.ext (congrArg (fun s : G.activeFaces => s.val) hij)
  rw [← Finset.card_image_of_injective t hinj]
  apply G.active_chain_card_le_four
  intro i hi j hj
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
  exact hchain i' hi' j' hj'

end Poincare.Topology.EmbeddedThreeFlagGrid
