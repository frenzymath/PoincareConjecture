import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected










set_option autoImplicit false

open Set
open scoped unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_closed_cut_based_edge_paths
    {X V κ ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (D : V → Set X) (C : κ → Set X)
    (hD : ∀ v, PLDomain e (D v)) (hconn : ∀ v, IsConnected (D v))
    (Y : κ → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, Nonempty (Y i)]
    (collar : ∀ i, (Y i × unitInterval) ≃ₜ C i)
    (endpoint : κ → Bool → V)
    (hport : ∀ i b y, (collar i (y, if b then 1 else 0) : X) ∈ D (endpoint i b)) :
    ∃ (p : ∀ v, D v) (y : ∀ i, Y i)
      (arm : ∀ i b, Path (p (endpoint i b) : X)
        (collar i (y i, if b then 1 else 0) : X))
      (core : ∀ i, Path (collar i (y i, 0) : X) (collar i (y i, 1) : X)),
      (∀ i b, range (arm i b) ⊆ D (endpoint i b)) ∧
      (∀ i t, core i t = (collar i (y i, t) : X)) ∧
      (∀ i, range (core i) ⊆ C i) ∧
      ∀ i, range (((arm i false).trans (core i)).trans (arm i true).symm) ⊆
        (D (endpoint i false) ∪ C i) ∪ D (endpoint i true) := by
  classical
  let p : ∀ v, D v := fun v => ⟨(hconn v).nonempty.choose, (hconn v).nonempty.choose_spec⟩
  let y : ∀ i, Y i := fun i => Classical.choice inferInstance
  have hpath (v : V) : PathConnectedSpace (D v) := by
    let : LocallyPathConnectedSpace (D v) := (hD v).locallyPathConnectedSpace
    let : ConnectedSpace (D v) := isConnected_iff_connectedSpace.mp (hconn v)
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  let armD (i : κ) (b : Bool) : Path (p (endpoint i b))
      (⟨collar i (y i, if b then 1 else 0), hport i b (y i)⟩ : D (endpoint i b)) :=
    @PathConnectedSpace.somePath _ _ (hpath (endpoint i b)) _ _
  let arm (i : κ) (b : Bool) : Path (p (endpoint i b) : X)
      (collar i (y i, if b then 1 else 0) : X) :=
    (armD i b).map continuous_subtype_val
  let core (i : κ) : Path (collar i (y i, 0) : X) (collar i (y i, 1) : X) := {
    toFun := fun t => collar i (y i, t)
    continuous_toFun := continuous_subtype_val.comp
      ((collar i).continuous.comp (continuous_const.prodMk continuous_id))
    source' := rfl
    target' := rfl }
  have harms (i : κ) (b : Bool) : range (arm i b) ⊆ D (endpoint i b) := by
    rintro _ ⟨t, rfl⟩
    exact (armD i b t).property
  have hcores (i : κ) : range (core i) ⊆ C i := by
    rintro _ ⟨t, rfl⟩
    exact (collar i (y i, t)).property
  refine ⟨p, y, arm, core, harms, fun _ _ => rfl, hcores, ?_⟩
  intro i
  rw [Path.trans_range, Path.trans_range, Path.symm_range]
  exact union_subset_union (union_subset_union (harms i false) (hcores i)) (harms i true)

end PoincareConjecture.M76
