import PoincareConjecture.Proofs.M76.Mathlib.ConvexFinitePLBoundary
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialGenerators









set_option autoImplicit false

open Set Geometry

namespace Set

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]




def IsFinitePLBallPair (s b : Set X) : Prop :=
  b ⊆ s ∧ ∃ c : Set E, IsCompact c ∧ Convex ℝ c ∧ (interior c).Nonempty ∧
    ∃ e : s ≃ₜ c, e.IsFinitePL ∧
      ∀ x : s, (x : X) ∈ b ↔ (e x : E) ∈ frontier c

variable {E}



theorem IsFinitePLBallPair.of_homeomorph {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {s b : Set X} {t c : Set Y} (ht : IsFinitePLBallPair E t c)
    (hb : b ⊆ s) (H : s ≃ₜ t) (hH : H.IsFinitePL)
    (hmem : ∀ x : s, (x : X) ∈ b ↔ (H x : Y) ∈ c) : IsFinitePLBallPair E s b := by
  obtain ⟨_, C, hC, hcv, hne, e, he, heb⟩ := ht
  exact ⟨hb, C, hC, hcv, hne, H.trans e, hH.trans he, fun x => (hmem x).trans (heb (H x))⟩



theorem isFinitePLBallPair_of_compact_convex {s : Set E}
    (hs : IsCompact s) (hcv : Convex ℝ s) (hne : (interior s).Nonempty)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hspace : K.space = s) :
    IsFinitePLBallPair E s (frontier s) := by
  refine ⟨hs.isClosed.frontier_subset, s, hs, hcv, hne, Homeomorph.refl s, ?_, fun _ => Iff.rfl⟩
  exact ⟨id, ⟨K, hK, hspace, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩, fun _ => rfl⟩




theorem isFinitePLBallPair_convexHull_finset (s : Finset E)
    (hind : AffineIndependent ℝ ((↑) : s → E))
    (hne : (interior (convexHull ℝ (s : Set E))).Nonempty) :
    IsFinitePLBallPair E (convexHull ℝ (s : Set E)) (frontier (convexHull ℝ (s : Set E))) := by
  have hi : ∀ r ∈ ({s} : Set (Finset E)), AffineIndependent ℝ ((↑) : r → E) := by
    rintro r rfl
    exact hind
  have hx : ∀ r ∈ ({s} : Set (Finset E)), ∀ t ∈ ({s} : Set (Finset E)),
      convexHull ℝ (r : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((r : Set E) ∩ t) := by
    rintro r rfl t rfl
    simp
  exact isFinitePLBallPair_of_compact_convex (s.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) hne (SimplicialComplex.ofGenerators {s} hi hx)
    (SimplicialComplex.finite_ofGenerators_faces (finite_singleton s) hi hx)
    (by rw [SimplicialComplex.space_ofGenerators]; simp)




theorem IsFinitePLBallPair.exists_extension [FiniteDimensional ℝ E] [FiniteDimensional ℝ X]
    {F Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {s b : Set X} {t c : Set Y} (hs : IsFinitePLBallPair E s b)
    (ht : IsFinitePLBallPair F t c) (eb : b ≃ₜ c) (heb : eb.IsFinitePL) :
    ∃ H : s ≃ₜ t, H.IsFinitePL ∧
      (∀ x : b, H ⟨x, hs.1 x.property⟩ = ⟨eb x, ht.1 (eb x).property⟩) ∧
      (∀ x : s, (x : X) ∈ b ↔ (H x : Y) ∈ c) := by
  obtain ⟨hb, S, hS, hScv, hSne, eX, heX, heXb⟩ := hs
  obtain ⟨hc, T, hT, hTcv, hTne, eY, heY, heYc⟩ := ht
  have htri := heb
  have htri' := heb.symm
  obtain ⟨_, ⟨K, hK, hKb, _⟩, _⟩ := htri
  obtain ⟨_, ⟨L, hL, hLc, _⟩, _⟩ := htri'
  let a := eX.restrictSubsets hb hS.isClosed.frontier_subset heXb
  let b' := eY.restrictSubsets hc hT.isClosed.frontier_subset heYc
  have ha : a.IsFinitePL := heX.restrictSubsets hb hS.isClosed.frontier_subset heXb K hK hKb
  have hb' : b'.IsFinitePL := heY.restrictSubsets hc hT.isClosed.frontier_subset heYc L hL hLc
  let d := a.symm.trans (eb.trans b')
  have hd : d.IsFinitePL := ha.symm.trans (heb.trans hb')
  obtain ⟨H, hH, hHd, _⟩ := hd.exists_convex_extension hS hT hScv hTcv hSne hTne
  let G := eX.trans (H.trans eY.symm)
  have hG : G.IsFinitePL := heX.trans (hH.trans heY.symm)
  have hGb (x : b) : G ⟨x, hb x.property⟩ = ⟨eb x, hc (eb x).property⟩ := by
    change eY.symm (H (eX ⟨x, hb x.property⟩)) = _
    have hxa : eX ⟨x, hb x.property⟩ = ⟨a x, hS.isClosed.frontier_subset (a x).property⟩ :=
      Subtype.ext rfl
    rw [hxa, hHd]
    apply eY.injective
    rw [eY.apply_symm_apply]
    apply Subtype.ext
    change (b' (eb (a.symm (a x))) : F) = (eY ⟨eb x, hc (eb x).property⟩ : F)
    rw [a.symm_apply_apply]
    rfl
  exact ⟨G, hG, hGb, G.mem_subset_iff_of_extension eb hb hc hGb⟩

end Set
