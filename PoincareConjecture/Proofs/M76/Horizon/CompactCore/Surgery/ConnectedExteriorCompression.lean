import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedExteriorCompression
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ConnectedProtectedCompressionComponent
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedCompressionLoops

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_connected_protected_exterior_compression
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K C F : Set X} {j : V2 → X}
    (he : PLDomain e K) (hK : IsCompact K) (hR : IsClosed R) (hKR : K ⊆ R)
    (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hC : IsClosed C) (hCconn : IsConnected C) (hCR : C ⊆ R)
    (hBC : frontier R ⊆ C) (hF : IsCompact F) (hFR : F ⊆ R)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K))
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) = (Subtype.val : R → X) ⁻¹' F)
    (hfront : frontier K = frontier R ∪ F)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x), ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hjext : MapsTo j D (interior K)ᶜ) (hjR : MapsTo j D R)
    (hjC : Disjoint (j '' D) C)
    (hproper : ∀ z : D, j z ∈ F ↔ (z : V2) ∈ Q) :
    ∃ H L : Set X,
      IsCompact H ∧ PLDomain e H ∧ K ∪ j '' D ⊆ interior H ∧
      L = H ∩ (interior K)ᶜ ∧ IsCompact L ∧ PLDomain e L ∧
      ∃ (P : OriginalDiskProduct e L j) (Fnew : Set X) (x : X) (M : Set X),
        MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) (interior H ∩ (R \ C)) ∧
        PLDomain e (K ∪ P.closedStrip) ∧ IsCompact (K ∪ P.closedStrip) ∧
        K ∪ P.closedStrip ⊆ R ∧
        P.closedStrip ∩ K = P.map '' (Q ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧
        Fnew = (F \ P.openStrip) ∪ P.endDisks ∧ IsCompact Fnew ∧
        frontier (K ∪ P.closedStrip) = frontier R ∪ Fnew ∧
        x ∈ C ∧ M = _root_.connectedComponentIn (K ∪ P.closedStrip) x ∧
        IsCompact M ∧ IsConnected M ∧ PLDomain e M ∧
        C ⊆ M ∧ M ⊆ K ∪ P.closedStrip ∧ M ⊆ R ∧
        (Fnew ∩ M).Nonempty ∧ IsCompact (Fnew ∩ M) ∧ Fnew ∩ M ⊆ interior R ∧
        Disjoint (frontier R) (Fnew ∩ M) ∧
        frontier M = frontier R ∪ (Fnew ∩ M) ∧
        frontier ((Subtype.val : R → X) ⁻¹' M) =
          (Subtype.val : R → X) ⁻¹' (Fnew ∩ M) ∧
        ((Subtype.val : R → X) ⁻¹' C ⊆ interior ((Subtype.val : R → X) ⁻¹' M)) ∧
        ((Subtype.val : R → X) ⁻¹' frontier R ⊆
          interior ((Subtype.val : R → X) ⁻¹' M)) ∧
        (∀ (y : R) (p : Path y y),
          (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' (Fnew ∩ M)) →
          ∃ H : p.Homotopy (Path.refl y), ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          IsOpen ((Subtype.val : L → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier L → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier K → X) ⁻¹'
            (P.map '' (Q ×ˢ Ioo (-ε) ε))) := by
  obtain ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew, hsmall,
    _, _, _, hnewPL, hnewcompact, hnewR, hfoot, heq, hFnew, hnewU,
    _, hnewfront, hnewrel, hnewprotect, _, _, _, hcollars⟩ :=
    he.exists_protected_exterior_compression_with_collars
      hK hR hKR hC hBC hFR hprotect hrel hfront hj hemb hjext hjR hjC hproper
  obtain ⟨_, _, hcut⟩ :=
    Set.protected_open_cut_region hC hBC hFR hprotect hrel hfront
  obtain ⟨hext, hextfront⟩ := he.compl_interior
  have hboundary : frontier (interior K)ᶜ ⊆ interior H := by
    rw [hextfront]
    exact he.closed.frontier_subset.trans (fun _ hx => hcore (Or.inl hx))
  have hLfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ) := by
    rw [hLE, Set.frontier_inter_of_frontier_subset_interior hPH.closed hext.closed
      hboundary, hextfront]
  have hFH : F ⊆ interior H := by
    intro y hy
    exact hcore (Or.inl (he.closed.frontier_subset (hfront.symm.subset (Or.inr hy))))
  have hlocal := protected_local_exterior_frontier hcut hFH hLfront
  have hrawloops := P.protected_compression_frontier_loops hF hlocal
    inter_subset_right hsmall
    (hcollars (3 / 4) (by norm_num) (by norm_num)).2.1 hloops
  have hnewint : Fnew ⊆ interior R := by
    intro y hy
    exact (mem_interior_iff_notMem_frontier (hnewU hy).1).mpr
      (fun h => (hnewU hy).2 (hBC h))
  obtain ⟨x, M, hx, hM, hMc, hMconn, hMPL, hCM, hMsub, hMR,
    hne, hMFc, hMFi, hdisj, hMfront, hMrel, hMprotect, hMBprotect⟩ :=
    hnewPL.exists_connected_protected_compression_component hnewcompact hnewR
      hRconn hend hCconn hCR hBC hFnew hnewint hnewfront hnewrel hnewprotect
  refine ⟨H, L, hH, hPH, hcore, hLE, hL, hPL, P, Fnew, x, M,
    hsmall, hnewPL, hnewcompact, hnewR, hfoot, heq, hFnew, hnewfront,
    hx, hM, hMc, hMconn, hMPL, hCM, hMsub, hMR, hne, hMFc, hMFi, hdisj,
    hMfront, hMrel, hMprotect, hMBprotect, ?_, hcollars⟩
  intro y p hp
  apply hrawloops y p
  intro t
  exact heq.subset (hp t).1

end PoincareConjecture.M76
