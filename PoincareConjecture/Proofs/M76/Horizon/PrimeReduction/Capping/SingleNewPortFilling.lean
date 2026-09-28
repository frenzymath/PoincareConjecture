import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalPuncturedCapFilling
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.isFinitePLBallPair_single_new_port_filling
    {X E F α κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : α → OpenPartialHomeomorph X V3} {R C : Set X} {f : X → E}
    (c : MarkedSphereCut e R κ) (d : MarkedSphereCut e R (Option κ))
    (hports : ∀ j : κ × Bool, d.ports (some j.1, j.2) = c.ports j)
    (hdc : d.carrier ⊆ c.carrier) (hC : IsClosed C) (hCd : C ⊆ d.carrier)
    (hm : HasPuncturedSphereModel e f C)
    (hfront : frontier C = ⋃ j : {j : Option κ × Bool // d.ports j ⊆ C}, d.ports j)
    (side : Bool) (hchosen : d.ports (none, side) ⊆ C)
    (hopposite : Disjoint (d.ports (none, !side)) C)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (phi : X → F) (hphi : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi c.carrier) (caps : κ × Bool → Set F)
    (hcaps : ∀ j, IsFinitePLBallPair V3 (caps j) (phi '' c.ports j))
    (hcontact : ∀ j, caps j ∩ phi '' c.carrier = phi '' c.ports j)
    (hcapsdis : Pairwise fun j k => Disjoint (caps j) (caps k)) :
    IsFinitePLBallPair V3
      (phi '' C ∪ ⋃ j : {j : κ × Bool // c.ports j ⊆ C}, caps j)
      (phi '' d.ports (none, side)) ∧
    (phi '' C ∪ ⋃ j : {j : κ × Bool // c.ports j ⊆ C}, caps j) ⊆
      phi '' c.carrier ∪ ⋃ j, caps j := by
  classical
  let J := {j : κ × Bool // c.ports j ⊆ C}
  let P : Option J → Set X := fun z => z.elim (d.ports (none, side)) (fun j => c.ports j)
  let q : Option J → Option κ × Bool :=
    fun z => z.elim (none, side) (fun j => (some j.val.1, j.val.2))
  have hqP (j : Option J) : d.ports (q j) = P j := by
    cases j with
    | none => rfl
    | some j => exact hports j
  have hqi : Function.Injective q := by
    intro j k h
    cases j with
    | none => cases k <;> simp_all [q]
    | some j =>
      cases k with
      | none => simp [q] at h
      | some k =>
        apply congrArg some
        apply Subtype.ext
        simpa only [q, Option.elim_some, Prod.mk.injEq, Option.some.injEq,
          ← Prod.ext_iff] using h
  have hPsub (j : Option J) : P j ⊆ C := by
    cases j with
    | none => exact hchosen
    | some j => exact j.property
  have hPfront : frontier C = ⋃ j, P j := by
    rw [hfront]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨⟨⟨i, b⟩, hj⟩, hxj⟩ := mem_iUnion.mp hx
      cases i with
      | none =>
        have hb : b = side := by
          by_contra hne
          have hb : b = !side := by cases b <;> cases side <;> simp_all
          obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := V3) (x := 0) (r := 1)).mpr zero_le_one
          let z := (d.portPL (none, b)).parametrization ⟨y, hy⟩
          exact disjoint_left.mp hopposite (hb ▸ z.property) (hj z.property)
        exact mem_iUnion.mpr ⟨none, by simpa only [P, Option.elim_none, hb] using hxj⟩
      | some i =>
        have hj' : c.ports (i, b) ⊆ C := by simpa only [hports (i, b)] using hj
        exact mem_iUnion.mpr ⟨some ⟨(i, b), hj'⟩, by
          simpa only [P, Option.elim_some, hports (i, b)] using hxj⟩
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨q j, by rw [hqP]; exact hPsub j⟩, by rwa [hqP]⟩
  have hPdis : Pairwise fun j k => Disjoint (P j) (P k) := by
    intro j k hjk
    rw [← hqP, ← hqP]
    exact d.portDisjoint (hqi.ne hjk)
  let old : {j : Option J // j ≠ none} → J :=
    fun j => j.val.get (Option.ne_none_iff_isSome.mp j.property)
  have hold (j : {j : Option J // j ≠ none}) : some (old j) = j.val :=
    Option.some_get (Option.ne_none_iff_isSome.mp j.property)
  have holdi : Function.Injective old := by
    intro j k h
    apply Subtype.ext
    rw [← hold j, ← hold k, h]
  let D : {j : Option J // j ≠ none} → Set F := fun j => caps (old j)
  have hD (j : {j : Option J // j ≠ none}) :
      IsFinitePLBallPair V3 (D j) (phi '' P j) := by
    change IsFinitePLBallPair V3 (caps (old j)) (phi '' P j.val)
    rw [← hold j]
    exact hcaps (old j)
  have hDcontact (j : {j : Option J // j ≠ none}) : D j ∩ phi '' C = phi '' P j := by
    change caps (old j) ∩ phi '' C = phi '' P j.val
    rw [← hold j]
    change caps (old j) ∩ phi '' C = phi '' c.ports (old j)
    apply Subset.antisymm
    · exact fun _ hx => (hcontact (old j)).subset
        ⟨hx.1, image_mono (hCd.trans hdc) hx.2⟩
    · intro x hx
      exact ⟨(hcaps (old j)).1 hx, image_mono (old j).property hx⟩
  have hDdis : Pairwise fun j k => Disjoint (D j) (D k) := by
    intro j k hjk
    apply hcapsdis
    intro h
    exact hjk (holdi (Subtype.ext h))
  have hball := hm.isFinitePLBallPair_cap_filling_original_image hC K g hg hgi
    (fun x hx => hreal x ((hCd.trans hdc hx).1)) P
    (fun j => hqP j ▸ d.portPL (q j)) hPdis hPfront phi hphi
    (hphii.mono (hCd.trans hdc)) none D hD hDcontact hDdis
  have hDunion : (⋃ j, D j) = ⋃ j : J, caps j := by
    apply Subset.antisymm
    · exact iUnion_subset (fun j => subset_iUnion (fun k : J => caps k) (old j))
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨some j, Option.some_ne_none j⟩, hxj⟩
  rw [hDunion] at hball
  refine ⟨hball, union_subset (image_mono (hCd.trans hdc) |>.trans subset_union_left) ?_⟩
  exact iUnion_subset (fun j => (subset_iUnion caps j.val).trans subset_union_right)

end PoincareConjecture.M76
