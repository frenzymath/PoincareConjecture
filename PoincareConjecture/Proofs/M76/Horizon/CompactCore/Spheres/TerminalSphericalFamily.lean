import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.MinimalCoreDiskIncompressibility
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.ProtectedMarkedCutFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Disks.EssentialCutDiskProjection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopTheorem










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1



theorem exists_original_terminal_spherical_family
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R A : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hB : IsCompact (frontier R))
    (hend : HasOneSimplyConnectedEnd R) (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ (n : ℕ) (K : Set X) (S : Fin n → Set X),
      IsCompact K ∧ IsConnected K ∧ K ⊆ R ∧ PLDomain e K ∧
      (∀ i, Nonempty (ChartwisePLSphere e (S i))) ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      (∀ i, S i ⊆ interior R) ∧
      frontier K = frontier R ∪ (⋃ i, S i) ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' K) := by
  classical
  obtain ⟨C, K, F, hC, _hCconn, _hCPL, _hCR, hBC, hCprotect,
    hK, hKconn, hKPL, _hCK, hKR, hFne, hF, hFi, hBF, hfront, hrel,
    hprotect, hloops, hincompressible⟩ :=
    exists_protected_core_without_essential_disk e hR hRconn hB hend hA hAR
  obtain ⟨_hY, hFY, hcut⟩ := Set.protected_open_cut_region hC.isClosed hBC
    (hFi.trans interior_subset) hprotect hrel hfront
  obtain ⟨n, S, _hn, hcover, hdisjoint, hcomponents, halt⟩ :=
    hKPL.exists_new_frontier_spheres_or_marked_cut_fillings hK hF hFne
      (hFi.trans interior_subset) hBF hfront hC hBC hprotect hrel hloops
  have hS : ∀ i, Nonempty (ChartwisePLSphere e (S i)) := by
    intro i
    rcases halt i with hsphere | ⟨d, P, hP, _hside, hPfront, hsource, hval,
      g, gamma, hg, hgP, hgamma, hessential⟩
    · exact hsphere
    · exfalso
      let f : C(D, P) := ⟨fun x => ⟨g x, hgP x.property⟩,
        (continuousOn_iff_continuous_domRestrict.mp hg.continuousOn).subtype_mk _⟩
      have hmark : (Subtype.val : ↥(R \ C) → X) ⁻¹' F ⊆ frontier P :=
        hPfront.symm.subset
      have hopen : IsOpen ((Subtype.val : frontier P → ↥(R \ C)) ⁻¹'
          ((Subtype.val : ↥(R \ C) → X) ⁻¹' F)) := by
        have heq : (Subtype.val : frontier P → ↥(R \ C)) ⁻¹'
            ((Subtype.val : ↥(R \ C) → X) ⁻¹' F) = univ := by
          ext x
          exact iff_of_true (hPfront.subset x.property) (mem_univ x)
        rw [heq]
        exact isOpen_univ
      obtain ⟨disk⟩ := Dehn.nonempty_marked_boundary_PL_loop_disk d P hP _ hmark
        hopen f gamma hgamma ⊥ inferInstance
        (fun h => hessential (Subgroup.mem_bot.mp h))
      obtain ⟨rim, hj, hemb, hjY, hrim, hproper, hout, _⟩ :=
        disk.project_protected_cut hKPL hcut hFY hsource hval hPfront
      exact hout (hincompressible _ hj hemb hjY hproper rim (fun u => (hrim u).symm))
  refine ⟨n, K, S, hK, hKconn, hKR, hKPL, hS, hdisjoint,
    fun i => (hcomponents i).2.2.1.trans hFi, ?_, ?_⟩
  · simpa only [hcover] using hfront
  · exact fun x hx => hprotect (interior_subset (hCprotect hx))

end PoincareConjecture.M76
