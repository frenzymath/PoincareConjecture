import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences
import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood

set_option autoImplicit false

open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76

private theorem exists_cap_ball_in_box
    {ι : Type*} [Fintype ι] (hdim : Fintype.card ι = 3)
    {a b : ι → ℝ} {d o q : Set (ι → ℝ)}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (ho : IsFinitePLBallPair (ℝ × ℝ) o q)
    (hdo : d ∩ o = q) (hbox : d ∪ o ⊆ Icc a b) :
    ∃ C : Set (ι → ℝ), IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (d ∪ o) ∧
      C ⊆ Icc a b := by
  classical
  obtain ⟨e, he, _, _⟩ := hd.exists_sphere_model_of_disk_union ho hdo
  obtain ⟨K, hK, hcv, hSK⟩ :=
    (hd.isCompact.union ho.isCompact).exists_finite_convex_neighborhood
  have hne : (interior K.space).Nonempty := by
    obtain ⟨x, hx, _⟩ := hd.sdiff_nonempty
    exact ⟨x, hSK (Or.inl hx)⟩
  have hhalf : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  obtain ⟨U, hU, _, hUf, _, hUB, _⟩ := he.hasAlexanderRegionBalls
    (isCompact_halfBall (Or.inl rfl)) hhalf (interior_halfBall_nonempty (Or.inl rfl))
    (by simp [Module.finrank_prod]) (by simpa using hdim)
    (K.isCompact_space_of_finite hK) hcv hne hSK K hK rfl
  refine ⟨closure U, hUB, ?_⟩
  have hUb : Bornology.IsBounded U := hUB.isCompact.isBounded.subset subset_closure
  intro x hx
  constructor
  · intro i
    let A : (ι → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj i).toAffineMap
    have hv : 0 < (-A).linear (-(Pi.single i 1)) := by simp [A]
    have hle := hU.affine_le_on_closure_of_le_frontier hUb (-A) _ hv
      (a := -a i) (fun y hy => by
        change -y i ≤ -a i
        exact neg_le_neg ((hbox (hUf ▸ hy)).1 i)) x hx
    change -x i ≤ -a i at hle
    linarith
  · intro i
    let A : (ι → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj i).toAffineMap
    have hv : 0 < A.linear (Pi.single i 1) := by simp [A]
    exact hU.affine_le_on_closure_of_le_frontier hUb A _ hv
      (a := b i) (fun y hy => (hbox (hUf ▸ hy)).2 i) x hx

private theorem ball_contact_of_outer_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    {W C S T D L : Set E}
    (hW : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) W S)
    (hC : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C T)
    (hWL : W ⊆ L) (hCL : C ⊆ L)
    (hT : T ⊆ S ∪ frontier L) (hST : S ∩ T = D)
    (hwitness : ((W ∩ frontier L) \ T).Nonempty) : W ∩ C = D := by
  have hd : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  have havoid : Disjoint (frontier (interior C)) (interior W) := by
    rw [hC.frontier_interior_of_finrank_eq hd]
    apply Set.disjoint_left.mpr
    intro x hxT hxW
    rcases hT hxT with hxS | hxL
    · have hxF : x ∈ frontier W := (hW.frontier_eq_of_finrank_eq hd).symm ▸ hxS
      exact hxF.2 hxW
    · exact hxL.2 (interior_mono hWL hxW)
  have hdis : Disjoint (interior W) (interior C) := by
    apply Set.disjoint_left.mpr
    intro x hxW hxC
    have hsub := (hW.isConnected_interior_of_finrank_eq hd).isPreconnected
      |>.m76_subset_of_disjoint_frontier isOpen_interior havoid ⟨x, hxW, hxC⟩
    have hWC : W ⊆ C := by
      rw [← hW.closure_interior_of_finrank_eq hd,
        ← hC.closure_interior_of_finrank_eq hd]
      exact closure_mono hsub
    obtain ⟨y, ⟨hyW, hyL⟩, hyT⟩ := hwitness
    apply hyT
    rw [← hC.frontier_eq_of_finrank_eq hd]
    exact ⟨subset_closure (hWC hyW), fun hy => hyL.2 (interior_mono hCL hy)⟩
  have heq := closure_inter_eq_frontier_inter_of_disjoint_open
    isOpen_interior isOpen_interior hdis
  rwa [hW.closure_interior_of_finrank_eq hd, hC.closure_interior_of_finrank_eq hd,
    hW.frontier_interior_of_finrank_eq hd, hC.frontier_interior_of_finrank_eq hd,
    hST] at heq

private theorem ball_eq_of_same_outer_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    {K L : Set E}
    (hK : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) K (frontier L))
    (hL : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) L (frontier L))
    (hKL : K ⊆ L) : K = L := by
  have hd : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = Module.finrank ℝ E := by
    simp [Module.finrank_prod, hdim]
  apply Subset.antisymm hKL
  have havoid : Disjoint (frontier (interior K)) (interior L) := by
    rw [hK.frontier_interior_of_finrank_eq hd]
    exact Set.disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  obtain ⟨x, hx⟩ := (hK.isConnected_interior_of_finrank_eq hd).nonempty
  have hsub := (hL.isConnected_interior_of_finrank_eq hd).isPreconnected
    |>.m76_subset_of_disjoint_frontier isOpen_interior havoid
      ⟨x, interior_mono hKL hx, hx⟩
  rw [← hL.closure_interior_of_finrank_eq hd, ← hK.closure_interior_of_finrank_eq hd]
  exact closure_mono hsub

private theorem boundary_without_disk_interior
    {X : Type*} {b d q : Set X} (hbd : b ∩ d = q) :
    (b ∪ d) \ (d \ q) = b := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    rcases hx with hxb | hxd
    · exact hxb
    · have hxq : x ∈ q := by
        by_contra h
        exact hn ⟨hxd, h⟩
      exact (hbd.symm.subset hxq).1
  · intro hxb
    exact ⟨Or.inl hxb, fun hx => hx.2 (hbd.subset ⟨hxb, hx.1⟩)⟩

theorem exists_hamilton_indexTwo_cap_regions
    {ι : Type*} [Fintype ι] (hdim : Fintype.card ι = 3)
    {a b : ι → ℝ} {B sigma d₀ d₁ o₀ o₁ q₀ q₁ : Set (ι → ℝ)}
    (hL : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (Icc a b) (frontier (Icc a b)))
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B ((sigma ∪ d₀) ∪ d₁))
    (hBL : B ⊆ Icc a b)
    (hd₀ : IsFinitePLBallPair (ℝ × ℝ) d₀ q₀)
    (hd₁ : IsFinitePLBallPair (ℝ × ℝ) d₁ q₁)
    (ho₀ : IsFinitePLBallPair (ℝ × ℝ) o₀ q₀)
    (ho₁ : IsFinitePLBallPair (ℝ × ℝ) o₁ q₁)
    (hdo₀ : d₀ ∩ o₀ = q₀) (hdo₁ : d₁ ∩ o₁ = q₁)
    (hdS₀ : d₀ ∩ sigma = q₀) (hdS₁ : d₁ ∩ sigma = q₁)
    (hdd : Disjoint d₀ d₁) (hoo : Disjoint o₀ o₁)
    (hSo₀ : ((sigma ∪ d₀) ∪ d₁) ∩ o₀ = q₀)
    (hSo₁ : ((sigma ∪ d₀) ∪ d₁) ∩ o₁ = q₁)
    (hfront : frontier (Icc a b) = (sigma ∪ o₀) ∪ o₁)
    (hq₁ : q₁.Nonempty) :
    ∃ C₀ C₁ : Set (ι → ℝ),
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C₀ (d₀ ∪ o₀) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C₁ (d₁ ∪ o₁) ∧
      C₀ ⊆ Icc a b ∧ C₁ ⊆ Icc a b ∧ B ∩ C₀ = d₀ ∧
      (B ∪ C₀) ∩ C₁ = d₁ ∧ (B ∪ C₀) ∪ C₁ = Icc a b := by
  have hdimV : Module.finrank ℝ (ι → ℝ) = 3 := by simpa using hdim
  have hqS₀ : q₀ ⊆ sigma := fun _ hx => (hdS₀.symm.subset hx).2
  have hqS₁ : q₁ ⊆ sigma := fun _ hx => (hdS₁.symm.subset hx).2
  have hoF₀ : o₀ ⊆ frontier (Icc a b) := fun _ hx => hfront.symm ▸ Or.inl (Or.inr hx)
  have hoF₁ : o₁ ⊆ frontier (Icc a b) := fun _ hx => hfront.symm ▸ Or.inr hx
  have hsigF : sigma ⊆ frontier (Icc a b) :=
    fun _ hx => hfront.symm ▸ Or.inl (Or.inl hx)
  have hdB₀ : d₀ ⊆ B := fun _ hx => hB.1 (Or.inl (Or.inr hx))
  have hdB₁ : d₁ ⊆ B := fun _ hx => hB.1 (Or.inr hx)
  obtain ⟨C₀, hC₀, hC₀L⟩ := exists_cap_ball_in_box hdim hd₀ ho₀ hdo₀
    (union_subset (hdB₀.trans hBL) (hoF₀.trans isClosed_Icc.frontier_subset))
  obtain ⟨C₁, hC₁, hC₁L⟩ := exists_cap_ball_in_box hdim hd₁ ho₁ hdo₁
    (union_subset (hdB₁.trans hBL) (hoF₁.trans isClosed_Icc.frontier_subset))
  have hcontact₀ : B ∩ C₀ = d₀ := by
    apply ball_contact_of_outer_frontier hdimV hB hC₀ hBL hC₀L
    · exact fun _ hx => hx.elim (fun h => Or.inl (Or.inl (Or.inr h)))
        (fun h => Or.inr (hoF₀ h))
    · ext x
      constructor
      · rintro ⟨hxS, hxd | hxo⟩
        · exact hxd
        · exact hd₀.1 (hSo₀.subset ⟨hxS, hxo⟩)
      · intro hxd
        exact ⟨Or.inl (Or.inr hxd), Or.inl hxd⟩
    · obtain ⟨y, hy⟩ := hq₁
      refine ⟨y, ⟨hB.1 (Or.inl (Or.inl (hqS₁ hy))), hsigF (hqS₁ hy)⟩, ?_⟩
      rintro (hyd | hyo)
      · exact Set.disjoint_left.mp hdd hyd (hd₁.1 hy)
      · exact Set.disjoint_left.mp hoo hyo (ho₁.1 hy)
  have hSout₀ : (((sigma ∪ d₀) ∪ d₁) \ d₀).Nonempty := by
    obtain ⟨x, hx, _⟩ := hd₁.sdiff_nonempty
    exact ⟨x, Or.inr hx, fun h => Set.disjoint_left.mp hdd h hx⟩
  have hTout₀ : ((d₀ ∪ o₀) \ d₀).Nonempty := by
    obtain ⟨x, hx, hxq⟩ := ho₀.sdiff_nonempty
    exact ⟨x, Or.inr hx, fun hd => hxq (hdo₀.subset ⟨hd, hx⟩)⟩
  have hWraw := hB.union_of_actual_disk_contact hC₀ hd₀
    (fun _ hx => Or.inl (Or.inr hx)) subset_union_left hSout₀ hTout₀ hcontact₀
  have hW : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B ∪ C₀) ((sigma ∪ o₀) ∪ d₁) := by
    have hrest : (sigma ∪ d₁) ∩ d₀ = q₀ := by
      ext x
      constructor
      · rintro ⟨hx | hx, hxd⟩
        · exact hdS₀.subset ⟨hxd, hx⟩
        · exact (Set.disjoint_left.mp hdd hxd hx).elim
      · intro hx
        exact ⟨Or.inl (hqS₀ hx), hd₀.1 hx⟩
    have hremove : ((sigma ∪ d₀) ∪ d₁) \ (d₀ \ q₀) = sigma ∪ d₁ := by
      rw [union_right_comm sigma d₀ d₁]
      exact boundary_without_disk_interior hrest
    have hcap : (d₀ ∪ o₀) \ (d₀ \ q₀) = o₀ := by
      rw [union_comm d₀ o₀]
      exact boundary_without_disk_interior ((inter_comm o₀ d₀).trans hdo₀)
    rw [hremove, hcap, union_right_comm sigma d₁ o₀] at hWraw
    exact hWraw
  have hWL : B ∪ C₀ ⊆ Icc a b := union_subset hBL hC₀L
  have hWo₁ : ((sigma ∪ o₀) ∪ d₁) ∩ o₁ = q₁ := by
    ext x
    constructor
    · rintro ⟨(hx | hx) | hx, hxo⟩
      · exact hSo₁.subset ⟨Or.inl (Or.inl hx), hxo⟩
      · exact (Set.disjoint_left.mp hoo hx hxo).elim
      · exact hSo₁.subset ⟨Or.inr hx, hxo⟩
    · intro hx
      exact ⟨Or.inl (Or.inl (hqS₁ hx)), ho₁.1 hx⟩
  have hcontact₁ : (B ∪ C₀) ∩ C₁ = d₁ := by
    apply ball_contact_of_outer_frontier hdimV hW hC₁ hWL hC₁L
    · exact fun _ hx => hx.elim (fun h => Or.inl (Or.inr h))
        (fun h => Or.inr (hoF₁ h))
    · ext x
      constructor
      · rintro ⟨hxS, hxd | hxo⟩
        · exact hxd
        · exact hd₁.1 (hWo₁.subset ⟨hxS, hxo⟩)
      · intro hxd
        exact ⟨Or.inr hxd, Or.inl hxd⟩
    · obtain ⟨y, hy, hyq⟩ := ho₀.sdiff_nonempty
      refine ⟨y, ⟨Or.inr (hC₀.1 (Or.inr hy)), hoF₀ hy⟩, ?_⟩
      rintro (hyd | hyo)
      · exact hyq (hSo₀.subset ⟨Or.inr hyd, hy⟩)
      · exact Set.disjoint_left.mp hoo hy hyo
  have hSout₁ : (((sigma ∪ o₀) ∪ d₁) \ d₁).Nonempty := by
    obtain ⟨x, hx, hxq⟩ := ho₀.sdiff_nonempty
    exact ⟨x, Or.inl (Or.inr hx), fun hd => hxq (hSo₀.subset ⟨Or.inr hd, hx⟩)⟩
  have hTout₁ : ((d₁ ∪ o₁) \ d₁).Nonempty := by
    obtain ⟨x, hx, hxq⟩ := ho₁.sdiff_nonempty
    exact ⟨x, Or.inr hx, fun hd => hxq (hdo₁.subset ⟨hd, hx⟩)⟩
  have hKraw := hW.union_of_actual_disk_contact hC₁ hd₁
    subset_union_right subset_union_left hSout₁ hTout₁ hcontact₁
  have hK : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) ((B ∪ C₀) ∪ C₁)
      (frontier (Icc a b)) := by
    have hrest : (sigma ∪ o₀) ∩ d₁ = q₁ := by
      ext x
      constructor
      · rintro ⟨hx | hx, hxd⟩
        · exact hdS₁.subset ⟨hxd, hx⟩
        · have hxq := hSo₀.subset ⟨Or.inr hxd, hx⟩
          exact (Set.disjoint_left.mp hdd (hd₀.1 hxq) hxd).elim
      · intro hx
        exact ⟨Or.inl (hqS₁ hx), hd₁.1 hx⟩
    have hremove := boundary_without_disk_interior hrest
    have hcap : (d₁ ∪ o₁) \ (d₁ \ q₁) = o₁ := by
      rw [union_comm d₁ o₁]
      exact boundary_without_disk_interior ((inter_comm o₁ d₁).trans hdo₁)
    rwa [hremove, hcap, ← hfront] at hKraw
  exact ⟨C₀, C₁, hC₀, hC₁, hC₀L, hC₁L, hcontact₀, hcontact₁,
    ball_eq_of_same_outer_frontier hdimV hK hL (union_subset hWL hC₁L)⟩

end PoincareConjecture.M76
