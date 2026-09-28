import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RetainedCollarReattachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem retained_collar_disjoint_other_cap_port
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K B : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e B)
    (F : V3 × ℝ → X) (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    (k q : Bool → Set V3) (hk : ∀ b, IsFinitePLBallPair P2 (k b) (q b))
    (hkS : ∀ b, k b ⊆ Sphere)
    (hcontact : ∀ b, (s.map '' k b) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q b)
    (hrim : ∀ b, s.map '' q b = P.capRimSet b)
    (hretDis : Disjoint (s.map '' k false) (s.map '' k true)) (b : Bool) :
    Disjoint (F '' (k b ×ˢ I)) ((s.map '' k (!b)) ∪ P.capDisk (!b)) := by
  have hret : Disjoint (s.map '' k b) (s.map '' k (!b)) := by
    cases b
    · exact hretDis
    · exact hretDis.symm
  obtain ⟨_, hHstrip, _, _, _⟩ := P.retained_collar_reattachment_geometry
    s F hF hFi hFK htop hstripK hband (hk b) (hkS b) (hcontact b) b (hrim b)
  apply disjoint_left.mpr
  intro x hxH hxother
  rcases hxother with hxret | hxcap
  · obtain ⟨z, hz, hzx⟩ := hxH
    obtain ⟨w, hw, hwx⟩ := hxret
    have heq : z = (w, 1) := hFi ⟨hkS b hz.1, hz.2⟩
      ⟨hkS (!b) hw, by norm_num⟩ (hzx.trans (hwx.symm.trans (htop w (hkS (!b) hw)).symm))
    have hzw : z.1 = w := congrArg Prod.fst heq
    exact disjoint_left.mp hret ⟨w, hzw ▸ hz.1, hwx⟩ ⟨w, hw, hwx⟩
  · have hxstrip : x ∈ P.closedStrip := by
      apply P.endDisks_subset_closedStrip
      rw [P.endDisks_eq_capDisks]
      cases b
      · exact Or.inr hxcap
      · exact Or.inl hxcap
    obtain ⟨z, hz, hzx⟩ := hHstrip.subset ⟨hxH, hxstrip⟩
    have ht : z.2 = 1 := hz.2
    have hzpair : z = (z.1, 1) := Prod.ext rfl ht
    have hxq : x ∈ s.map '' q b :=
      ⟨z.1, hz.1, (htop z.1 (hkS b ((hk b).1 hz.1))).symm.trans
        ((congrArg F hzpair).symm.trans hzx)⟩
    have hxcapb := P.capRimSet_subset_capDisk b ((hrim b).subset hxq)
    exact disjoint_left.mp (P.disjoint_capDisks b) hxcapb hxcap

theorem retained_collar_meets_selected_exchange_boundary
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K B N Other : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e B)
    (F : V3 × ℝ → X) (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere)
    (hcontact : (s.map '' k) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q)
    (b : Bool) (hrim : s.map '' q = P.capRimSet b)
    (hOther : Disjoint (F '' (k ×ˢ I)) Other)
    (hWclosed : IsClosed ((F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip))
    (hWfront : frontier ((F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip) = N ∪ Other) :
    (N ∩ (F '' (k ×ˢ I))).Nonempty := by
  obtain ⟨_, _, _, _, hmeet⟩ := P.retained_collar_reattachment_geometry
    s F hF hFi hFK htop hstripK hband hk hkS hcontact b hrim
  obtain ⟨_, hdis, _⟩ := P.retained_collar_exchange_exterior
    s F hF hFi hFK htop hstripK hband hk hkS hcontact b hrim K subset_rfl
  have hk2 := hk.model_equiv
    (ContinuousLinearEquiv.ofFinrankEq (by simp) : P2 ≃L[ℝ] V2)
  obtain ⟨z, hz⟩ := hk2.isConnected_boundary_two.nonempty
  have hx : F (z, 0) ∈
      ((F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip) ∩ (F '' (k ×ˢ I)) :=
    hmeet.symm.subset ⟨(z, 0), ⟨hz, by norm_num⟩, rfl⟩
  have hxf : F (z, 0) ∈ frontier ((F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip) := by
    rw [hWclosed.frontier_eq]
    exact ⟨hx.1, fun hi => disjoint_left.mp hdis hx.2 hi⟩
  have hxN : F (z, 0) ∈ N := (hWfront.subset hxf).resolve_right
    (fun ho => disjoint_left.mp hOther hx.2 ho)
  exact ⟨_, hxN, hx.2⟩

end PoincareConjecture.M76.OriginalDiskProduct
