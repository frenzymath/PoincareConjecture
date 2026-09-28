import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedBoundaryLabels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereDiskPortGluingOriginal

set_option autoImplicit false
open Set Geometry Geometry.CubicalThreeSphere

namespace PoincareConjecture.M76.HasPuncturedSphereModel

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem of_original_disk_attachment
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (R : Bool → Set X) (hR : ∀ b, IsCompact (R b))
    (hm : ∀ b, HasPuncturedSphereModel e f (R b))
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R false ∪ R true, f x ∈ K.space ∧ g (f x) = x)
    (B T : Bool → Set X) (hB : ∀ b, IsConnected (B b))
    (hBc : ∀ b, IsClosed (B b)) (hTc : ∀ b, IsClosed (T b))
    (hBT : ∀ b, Disjoint (B b) (T b))
    (hboundary : ∀ b, frontier (R b) = B b ∪ T b)
    {d q : Set X} (hqd : q ⊆ d)
    (hd : IsFinitePLBallPair (ℝ × ℝ) (f '' d) (f '' q))
    (hcontact : R false ∩ R true = d)
    (hdB : ∀ b, d ⊆ B b) (hout : ∀ b, (B b \ d).Nonempty)
    (hfront : frontier (R false ∪ R true) =
      ((B false \ (d \ q)) ∪ (B true \ (d \ q))) ∪ (T false ∪ T true)) :
    HasPuncturedSphereModel e f (R false ∪ R true) := by
  classical
  choose n A r M G C hA hAdis hG hC hmark using fun b => (hm b).2
  have hRU (b : Bool) : R b ⊆ R false ∪ R true := by
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hMK (b : Bool) : M b ⊆ K.space := by
    intro y hy
    let x := (G b).symm ⟨y, hy⟩
    have hval : f x = y := (hG b x).symm.trans
      (congrArg Subtype.val ((G b).apply_symm_apply _))
    exact hval ▸ (hreal x (hRU b x.property)).1
  have hginv (b : Bool) (x : R b) : g (G b x) = (x : X) := by
    rw [hG]
    exact (hreal x (hRU b x.property)).2
  have hlabels (b : Bool) := exists_original_punctured_model_boundary_spheres
    (hR b).isClosed K g hg hgi (hMK b) (G b) (hginv b)
    (A b) (r b) (fun i => (hA b i).1) (fun i => (hA b i).2.1)
    (hAdis b) (C b) (hC b) (hmark b)
  choose S sS hSval hSR hSdis hSf hSmark hSimage using hlabels
  have hselected (b : Bool) := (hB b).exists_eq_label_of_closed_partition
    (hBc b) (hTc b) (hBT b) (S b) (fun i => (sS b i).isConnected)
    (fun i => (sS b i).isCompact.isClosed) (hSdis b)
    ((hboundary b).symm.trans (hSf b))
  choose i hi hother hT using hselected
  have hfi : InjOn f (R false ∪ R true) := by
    intro x hx y hy hxy
    exact (hreal x hx).2.symm.trans ((congrArg g hxy).trans (hreal y hy).2)
  have hport (b : Bool) (x : R b) (hx : (x : X) ∈ d) :
      (C b (G b x) : V4) ∈ r b (i b) := by
    apply (hSmark b (i b) x).mp
    rw [hi]
    exact hdB b hx
  have houtside (b : Bool) : ∃ x : R b,
      (C b (G b x) : V4) ∈ r b (i b) ∧ (x : X) ∉ d := by
    obtain ⟨x, hxB, hxd⟩ := hout b
    have hxR : x ∈ R b := (hR b).isClosed.frontier_subset
      ((hboundary b).symm.subset (Or.inl hxB))
    refine ⟨⟨x, hxR⟩, ?_, hxd⟩
    exact (hSmark b (i b) ⟨x, hxR⟩).mp ((hi b).symm ▸ hxB)
  have hset (b : Bool) (j : Fin (n b)) :
      (Subtype.val : R b → X) ''
        ((fun x : R b => (C b (G b x) : V4)) ⁻¹' r b j) = S b j := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hSmark b j x).mpr hx
    · intro x hx
      exact ⟨⟨x, hSR b j hx⟩, (hSmark b j ⟨x, hSR b j hx⟩).mp hx, rfl⟩
  apply of_disk_glued_marked_models R hR (hm false).1 hfi
    A r (fun b j => (hA b j).1) (fun b j => (hA b j).2.1)
    (fun b j => (hA b j).2.2) hAdis i M G hG C hC
    hqd hd hcontact hport houtside
  dsimp only
  simp only [hset, hi]
  rw [hfront]
  congr 1
  rw [hT false, hT true]
  ext x
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨false, j, hj⟩
    · exact ⟨true, j, hj⟩
  · rintro ⟨b, j, hj⟩
    cases b
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr ⟨j, hj⟩

end PoincareConjecture.M76.HasPuncturedSphereModel
