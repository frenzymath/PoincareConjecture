import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphSectionPasting
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutEdgePaths

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.CutGraph

local notation "V3" => (Fin 3 → ℝ)

theorem exists_closed_cut_graph_section
    {X V I ι : Type*} [TopologicalSpace X]
    [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {e : ι → OpenPartialHomeomorph X V3}
    (R : Set X) (D : V → Set X) (C : I → Set X)
    (hD : ∀ v, PLDomain e (D v)) (hconn : ∀ v, IsConnected (D v))
    (hDR : ∀ v, D v ⊆ R) (hCR : ∀ i, C i ⊆ R)
    (Y : I → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, Nonempty (Y i)]
    (W : ∀ i, (Y i × unitInterval) ≃ₜ C i) (ends : I → Bool → V)
    (hport : ∀ i b y, (W i (y, if b then 1 else 0) : X) ∈ D (ends i b)) :
    ∃ (p : ∀ v, D v) (y : ∀ i, Y i) (s : C(carrier ends, R)),
      (∀ v (x : carrier ends), (x : Ambient V I) = vertex v → (s x : X) = p v) ∧
      (∀ i b (x : carrier ends), (x : Ambient V I) ∈ arm ends i b →
        (s x : X) ∈ D (ends i b)) ∧
      (∀ i (x : carrier ends) (hx : (x : Ambient V I) ∈ bridge i),
        (s x : X) = W i (y i, faceCoordinate (J := Coordinate V I)
          {Sum.inr (i, false), Sum.inr (i, true)} (Sum.inr (i, true))
          ⟨(x : Ambient V I), hx⟩)) := by
  obtain ⟨p, y, arms, cores, harms, hcores, _, _⟩ :=
    exists_closed_cut_based_edge_paths D C hD hconn Y W ends hport
  let a (v : V) : R := ⟨p v, hDR v (p v).property⟩
  let u (i : I) (b : Bool) : R :=
    ⟨W i (y i, if b then 1 else 0), hCR i (W i (y i, if b then 1 else 0)).property⟩
  let A (i : I) (b : Bool) : Path (a (ends i b)) (u i b) := {
    toFun := fun t => ⟨arms i b t, hDR _ (harms i b (mem_range_self t))⟩
    continuous_toFun := (arms i b).continuous.subtype_mk _
    source' := Subtype.ext (arms i b).source
    target' := Subtype.ext (arms i b).target }
  let K (i : I) : Path (u i false) (u i true) := {
    toFun := fun t => ⟨W i (y i, t), hCR i (W i (y i, t)).property⟩
    continuous_toFun := (continuous_subtype_val.comp
      ((W i).continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _
    source' := rfl
    target' := rfl }
  obtain ⟨s, hsv, hsa, hsk⟩ := exists_subdivided_path_map ends a u A K
  refine ⟨p, y, s, ?_, ?_, ?_⟩
  · intro v x hx
    exact congrArg Subtype.val (hsv v x hx)
  · intro i b x hx
    rw [hsa i b x hx]
    exact harms i b (mem_range_self _)
  · intro i x hx
    exact congrArg Subtype.val (hsk i x hx)

end PoincareConjecture.M76.CutGraph
