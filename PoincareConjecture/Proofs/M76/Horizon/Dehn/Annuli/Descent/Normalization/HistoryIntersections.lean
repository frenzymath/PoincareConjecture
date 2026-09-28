import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.FinalIntersection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.PrefixDoublePairs











set_option autoImplicit false

open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}



theorem Step.exists_relative_history_intersection_faces
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    {n : ℕ} (face : Fin n → Finset V) (hfaces : ∀ i, face i ∈ K.faces)
    (P : ℕ → SimplicialComplex ℝ V) (hPK : ∀ k ≤ n, P k ≤ K)
    (hPn : (P n).space = K.space)
    (hsucc : ∀ i : Fin n,
      (P (i.val + 1)).space = (P i.val).space ∪ convexHull ℝ (face i : Set V))
    (Q : Fin n → OpenPartialHomeomorph t.Carrier E)
    (B : Fin n → OpenPartialHomeomorph s.Carrier E)
    (J : Fin n → SimplicialComplex ℝ E)
    (hQ : ∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid E)
    (hval : ∀ i z, Q i z = B i (step.projection (step.inclusion z)))
    (hmaps : ∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source)
    (hJ : ∀ i, (J i).faces.Finite) (hJQ : ∀ i, (J i).space ⊆ (Q i).target)
    (N : K.faces → Set t.Carrier)
    (hselected : ∀ i, N ⟨face i, hfaces i⟩ ⊆
      (Q i).source ∩ (Q i) ⁻¹' (J i).space)
    (hNinj : ∀ a, InjOn (step.projection ∘ step.inclusion) (N a))
    {R : Set M} {boundary : Set V} (states : ℕ → RelativeSurfaceState t K N R boundary)
    (motions : ∀ i : Fin n,
      RelativeFaceMotionData step K (P i.val) (P (i.val + 1)) (states i.val).map
        (Q i) (B i) (J i) N R)
    (htransitions : ∀ i : Fin n,
      (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map)
    (hstable : ∀ i k, i ≤ k → k ≤ n →
      EqOn (states k).map (states i).map (P i).space)
    (hzero : InjOn ((step.projection ∘ step.inclusion) ∘ (states 0).map) (P 0).space)
    {x y : V} (hx : x ∈ K.space) (hy : y ∈ K.space) (hne : x ≠ y)
    (hxy : step.projection (step.inclusion ((states n).map x)) =
      step.projection (step.inclusion ((states n).map y))) :
    ∃ (i : Fin n) (x' y' : V) (old : (P i.val).faces) (a b : Finset E),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ convexHull ℝ (face i : Set V) ∧ x' ∉ (P i.val).space ∧
      y' ∈ intrinsicInterior ℝ (convexHull ℝ (old.val : Set V)) ∧
      a ∈ (motions i).freeComplex.faces ∧ a ∉ (motions i).fixedComplex.faces ∧
      b ∈ ((motions i).targets old).faces ∧
      Q i ((states n).map x') ∈ intrinsicInterior ℝ
        (convexHull ℝ ((motions i).coordinates.map 1 '' (a : Set E))) ∧
      B i (step.projection (step.inclusion ((states n).map y'))) ∈
        intrinsicInterior ℝ (convexHull ℝ (b : Set E)) ∧
      a.card ≤ (face i).card ∧ b.card ≤ old.val.card ∧
      affineSpan ℝ ((motions i).coordinates.map 1 '' (a : Set E) ∪ (b : Set E)) = ⊤ ∧
      Module.finrank ℝ ((affineSpan ℝ ((motions i).coordinates.map 1 '' (a : Set E)) ⊓
        affineSpan ℝ (b : Set E)).direction) + Module.finrank ℝ E =
        (a.card - 1) + (b.card - 1) := by
  let g := (step.projection ∘ step.inclusion) ∘ (states n).map
  have hinitial : InjOn g (P 0).space := by
    intro u hu v hv huv
    apply hzero hu hv
    change step.projection (step.inclusion ((states 0).map u)) =
      step.projection (step.inclusion ((states 0).map v))
    rw [← hstable 0 n (Nat.zero_le _) le_rfl hu,
      ← hstable 0 n (Nat.zero_le _) le_rfl hv]
    exact huv
  have hcell (i : Fin n) : InjOn g (convexHull ℝ (face i : Set V)) := by
    intro u hu v hv huv
    have heq : (states n).map u = (states n).map v :=
      hNinj ⟨face i, hfaces i⟩ ((states n).retained _ hu) ((states n).retained _ hv) huv
    exact congrArg Subtype.val ((states n).embedding.injective
      (a₁ := ⟨u, K.convexHull_subset_space (hfaces i) hu⟩)
      (a₂ := ⟨v, K.convexHull_subset_space (hfaces i) hv⟩) heq)
  obtain ⟨i, x', y', hswap, hxface, hxold, hyold, hpair⟩ :=
    exists_active_prefix_of_double_pair (fun k ↦ (P k).space)
      (fun i ↦ convexHull ℝ (face i : Set V)) hsucc g hinitial hcell
      (hPn.symm.subset hx) (hPn.symm.subset hy) hne hxy
  obtain ⟨oldFace, holdFace, hyface⟩ := (P i.val).exists_face_intrinsicInterior_of_finite
    (hK.subset (hPK i.val i.isLt.le)) hyold
  let old : (P i.val).faces := ⟨oldFace, holdFace⟩
  have hinj : InjOn (states i.val).map K.space := by
    intro z hz w hw hzw
    exact congrArg Subtype.val ((states i.val).embedding.injective
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw)
  have hold := hstable i.val n i.isLt.le le_rfl
  have hnext : EqOn (states n).map ((motions i).ambient 1 ∘ (states i.val).map)
      (P (i.val + 1)).space := by
    intro z hz
    exact (hstable (i.val + 1) n (by omega) le_rfl hz).trans
      (congrFun (htransitions i) z)
  have hxwindow := hselected i ((states i.val).retained ⟨face i, hfaces i⟩ hxface)
  obtain ⟨a, b, ha, ha0, hb, hxa, hyb, hacard, hbcard, hspan, hrank⟩ :=
    (motions i).exists_final_intersection_faces hK (hPK i.val i.isLt.le)
      (hfaces i) (hsucc i) (states i.val).original_PL hinj (hQ i) (hval i) (hmaps i)
      (hJ i) (hJQ i) hold hnext hxface hxold hxwindow.1 hxwindow.2 old
      (intrinsicInterior_subset hyface) hpair
  exact ⟨i, x', y', old, a, b, hswap, hxface, hxold, hyface,
    ha, ha0, hb, hxa, hyb, hacard, hbcard, hspan, hrank⟩

end Geometry.OriginalPLTower
