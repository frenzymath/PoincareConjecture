import PoincareConjecture.Proofs.M76.Wall.BoundaryExitPath
import PoincareConjecture.Proofs.M76.Wall.OpenPLPath
import PoincareConjecture.Proofs.M76.Wall.SimplePLArc
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLPathOperations










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem PLDomain.exists_protected_simple_arc
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L W : Set X}
    (hL : PLDomain e L) (hW : IsOpen W) (hconn : IsConnected (W \ L))
    {a b : X} (ha : a ∈ frontier L) (haW : a ∈ W)
    (hb : b ∈ frontier L) (hbW : b ∈ W) (hab : a ≠ b) :
    ∃ q : ℝ → X, PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) ∧
      InjOn q (Icc (0 : ℝ) 1) ∧ q 0 = a ∧ q 1 = b ∧
      MapsTo q (Icc (0 : ℝ) 1) W ∧
      ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ L ↔ t = 0 ∨ t = 1 := by
  classical
  let := ChartedSpace.ofChartCover e hL.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨qa, hqa, hqa0, hqaW, hqaL⟩ := hL.exists_boundary_exit_path hW ha haW
  obtain ⟨qb, hqb, hqb0, hqbW, hqbL⟩ := hL.exists_boundary_exit_path hW hb hbW
  have hqa1 : qa 1 ∈ W \ L :=
    ⟨hqaW hone, fun h => one_ne_zero ((hqaL 1 hone).mp h)⟩
  have hqb1 : qb 1 ∈ W \ L :=
    ⟨hqbW hone, fun h => one_ne_zero ((hqbL 1 hone).mp h)⟩
  obtain ⟨qm, hqm, hqm0, hqm1, hqmU⟩ :=
    OpenPartialHomeomorph.exists_polyhedralPL_path_in_open e hL.compatible hL.cover
      (hW.sdiff hL.closed) hconn hqa1 hqb1
  let pa : Path a (qa 1) := Path.ofLine hqa.continuousOn hqa0 rfl
  let pb : Path b (qb 1) := Path.ofLine hqb.continuousOn hqb0 rfl
  let pm : Path (qa 1) (qb 1) := Path.ofLine hqm.continuousOn hqm0 hqm1
  have hpa : PolyhedralPLInCharts e pa.extend (Icc (0 : ℝ) 1) :=
    hqa.congr (fun _ ht => (pa.extend_apply ht).symm)
  have hpb : PolyhedralPLInCharts e pb.extend (Icc (0 : ℝ) 1) :=
    hqb.congr (fun _ ht => (pb.extend_apply ht).symm)
  have hpm : PolyhedralPLInCharts e pm.extend (Icc (0 : ℝ) 1) :=
    hqm.congr (fun _ ht => (pm.extend_apply ht).symm)
  let p : Path a b := (pa.trans pm).trans pb.symm
  have hp : PolyhedralPLInCharts e p.extend (Icc (0 : ℝ) 1) :=
    (pa.trans pm).polyhedralPL_extend_trans hL.cover hL.compatible pb.symm
      (pa.polyhedralPL_extend_trans hL.cover hL.compatible pm hpa hpm)
      (pb.polyhedralPL_extend_symm hpb)
  have himage : p.extend '' Icc (0 : ℝ) 1 = (range pa ∪ range pm) ∪ range pb := by
    rw [p.image_extend_of_subset subset_rfl]
    change range ((pa.trans pm).trans pb.symm) = _
    rw [Path.trans_range, Path.trans_range, Path.symm_range]
  have hpW : p.extend '' Icc (0 : ℝ) 1 ⊆ W := by
    rw [himage]
    rintro y ((⟨t, rfl⟩ | ⟨t, rfl⟩) | ⟨t, rfl⟩)
    · exact hqaW t.property
    · exact (hqmU t.property).1
    · exact hqbW t.property
  have hcontact {y : X} (hy : y ∈ p.extend '' Icc (0 : ℝ) 1)
      (hyL : y ∈ L) : y = a ∨ y = b := by
    rw [himage] at hy
    rcases hy with ((⟨t, rfl⟩ | ⟨t, rfl⟩) | ⟨t, rfl⟩)
    · left
      have ht := (hqaL t t.property).mp hyL
      change qa t = a
      rw [ht, hqa0]
    · exact False.elim ((hqmU t.property).2 hyL)
    · right
      have ht := (hqbL t t.property).mp hyL
      change qb t = b
      rw [ht, hqb0]
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hKconn : IsConnected K.space := by
    rw [hKs]
    exact isConnected_Icc zero_le_one
  have hpK : PolyhedralPLInCharts e p.extend K.space := hKs.symm ▸ hp
  have hpne : p.extend 0 ≠ p.extend 1 := by
    simpa only [p.extend_zero, p.extend_one] using hab
  obtain ⟨q, hq, hqi, hq0, hq1, hqimage⟩ :=
    OpenPartialHomeomorph.exists_simple_polyhedralPL_arc_in_image e hL.compatible
      hL.cover K hK hKconn hpK (hKs.symm.subset hzero) (hKs.symm.subset hone) hpne
  have hq0' : q 0 = a := hq0.trans p.extend_zero
  have hq1' : q 1 = b := hq1.trans p.extend_one
  have hqsub : q '' Icc (0 : ℝ) 1 ⊆ p.extend '' Icc (0 : ℝ) 1 := by
    simpa only [hKs] using hqimage
  refine ⟨q, hq, hqi, hq0', hq1', fun _ ht => hpW (hqsub ⟨_, ht, rfl⟩), ?_⟩
  intro t ht
  constructor
  · intro hqt
    rcases hcontact (hqsub ⟨t, ht, rfl⟩) hqt with h | h
    · exact Or.inl (hqi ht hzero (h.trans hq0'.symm))
    · exact Or.inr (hqi ht hone (h.trans hq1'.symm))
  · rintro (rfl | rfl)
    · rw [hq0']
      exact hL.closed.frontier_subset ha
    · rw [hq1']
      exact hL.closed.frontier_subset hb

end PoincareConjecture.M76
