use rand::Rng;

// Protocol parameters
const LAMBDA: usize = 128; // Total bit length
const BLOCK_SIZE: usize = 16; // ℓ - size of each block
const EPSILON: usize = 3; // Threshold distance per block
const NUM_BLOCKS: usize = LAMBDA / BLOCK_SIZE; // B = λ/ℓ

// Field prime (large prime for finite field F_p)
const FIELD_PRIME: i128 = 2147483647; // 2^31 - 1 (Mersenne prime)

/// Modular arithmetic helpers
fn mod_add(a: i128, b: i128, m: i128) -> i128 {
    ((a % m + b % m) % m + m) % m
}

fn mod_mul(a: i128, b: i128, m: i128) -> i128 {
    ((a % m) * (b % m) % m + m) % m
}

#[derive(Debug, Clone)]
struct Block {
    bits: Vec<u8>,
}

impl Block {
    fn new(bits: Vec<u8>) -> Self {
        assert_eq!(bits.len(), BLOCK_SIZE);
        assert!(bits.iter().all(|&b| b == 0 || b == 1));
        Block { bits }
    }

    fn hamming_distance(&self, other: &Block) -> usize {
        self.bits
            .iter()
            .zip(other.bits.iter())
            .map(|(&a, &b)| if a != b { 1 } else { 0 })
            .sum()
    }
}

#[derive(Debug, Clone)]
struct BinaryVector {
    blocks: Vec<Block>,
}

impl BinaryVector {
    fn new(bits: Vec<u8>) -> Self {
        assert_eq!(bits.len(), LAMBDA);
        assert!(bits.iter().all(|&b| b == 0 || b == 1));

        let blocks: Vec<Block> = bits
            .chunks(BLOCK_SIZE)
            .map(|chunk| Block::new(chunk.to_vec()))
            .collect();

        BinaryVector { blocks }
    }

    fn random() -> Self {
        let mut rng = rand::thread_rng();
        let bits: Vec<u8> = (0..LAMBDA).map(|_| rng.gen_range(0..2)).collect();
        BinaryVector::new(bits)
    }

    fn get_block(&self, block_idx: usize) -> &Block {
        &self.blocks[block_idx]
    }

    fn to_bits(&self) -> Vec<u8> {
        self.blocks.iter().flat_map(|b| b.bits.clone()).collect()
    }
}

type DatabaseEntry = BinaryVector;

struct Database {
    entries: Vec<DatabaseEntry>,
}

impl Database {
    fn random(n: usize) -> Self {
        let entries: Vec<DatabaseEntry> = (0..n).map(|_| BinaryVector::random()).collect();
        Database { entries }
    }
}

/// TTP Protocol - Fast Evaluation Version
///
/// Optimization rationale:
/// Instead of symbolically expanding each Z_{i,b}(d^(b)) polynomial (which explodes in term count
/// for λ=128, ℓ=16, ε=3), we evaluate the same polynomial numerically at query time.
/// For a given block distance D in {0..ℓ}:
///   Z_{i,b}(D) = ∏_{t=ε}^{ℓ} (D - t)
/// This preserves protocol semantics while reducing complexity from huge polynomial expansion
/// to O(n * B * (ℓ-ε+1)) scalar multiplications.
struct TTPProtocol {
    database: Database,
    /// Blinding values r_i for each database entry
    r_blinds: Vec<i128>,
}

impl TTPProtocol {
    fn new(database: Database) -> Self {
        let n = database.entries.len();
        let mut rng = rand::thread_rng();

        // Generate blinding values r_i ∈ F_p for each database entry
        let r_blinds: Vec<i128> = (0..n).map(|_| rng.gen_range(1..FIELD_PRIME)).collect();

        TTPProtocol { database, r_blinds }
    }

    /// Compute Z(D) = ∏_{t=ε}^{ℓ} (D - t) mod p for a concrete block distance D.
    ///
    /// Properties:
    /// - If D >= ε, one factor is zero, so Z(D) = 0
    /// - If D < ε, no factor is zero, so Z(D) != 0 in F_p
    fn threshold_value_for_distance(distance: usize) -> i128 {
        debug_assert!(distance <= BLOCK_SIZE);

        let mut z = 1i128;
        for t in EPSILON..=BLOCK_SIZE {
            z = mod_mul(z, distance as i128 - t as i128, FIELD_PRIME);
        }
        z
    }

    /// Build phase retained for protocol flow compatibility.
    /// The expensive symbolic construction is intentionally removed.
    fn build_entry_polynomials(&mut self) {
        println!("Building TTP per-entry representations (fast mode)...");
        println!("{}", "=".repeat(80));
        println!("Blinding values r_i: {:?}", &self.r_blinds);
        println!("No symbolic polynomial expansion is performed.");
        println!(
            "Runtime will remain practical for λ={}, ℓ={}, ε={}",
            LAMBDA, BLOCK_SIZE, EPSILON
        );
    }

    /// Client: Evaluate all S_i values directly:
    ///   S_i(d) = Σ_{b=1}^{B} Z_{i,b}(D_{i,b}(d)) + r_i
    fn client_evaluate(&self, client_query: &BinaryVector) -> Vec<i128> {
        self.database
            .entries
            .iter()
            .enumerate()
            .map(|(entry_idx, entry)| {
                let mut s_i = self.r_blinds[entry_idx];

                for b in 0..NUM_BLOCKS {
                    let distance = client_query
                        .get_block(b)
                        .hamming_distance(entry.get_block(b));
                    let z = Self::threshold_value_for_distance(distance);
                    s_i = mod_add(s_i, z, FIELD_PRIME);
                }

                s_i
            })
            .collect()
    }

    /// Server: Unmask and check results
    /// Returns true if ANY entry matches (at least one res_i ≠ 0 after unmasking)
    fn server_check(&self, res_values: &[i128]) -> (bool, Vec<usize>) {
        assert_eq!(res_values.len(), self.r_blinds.len());

        let mut matching_entries = Vec::new();

        for (i, &res_i) in res_values.iter().enumerate() {
            // Unmask: compute res_i - r_i
            let unmasked = mod_add(res_i, -self.r_blinds[i], FIELD_PRIME);

            // If unmasked ≠ 0: this entry matches
            if unmasked != 0 {
                matching_entries.push(i);
            }
        }

        let has_match = !matching_entries.is_empty();
        (has_match, matching_entries)
    }

    /// Verification: check if entry actually matches
    fn entry_matches(&self, entry_idx: usize, client_query: &BinaryVector) -> bool {
        let entry = &self.database.entries[entry_idx];
        (0..NUM_BLOCKS).all(|b| {
            client_query
                .get_block(b)
                .hamming_distance(entry.get_block(b))
                < EPSILON
        })
    }

    /// Get all actual matching entries (for verification)
    fn get_actual_matches(&self, client_query: &BinaryVector) -> Vec<usize> {
        (0..self.database.entries.len())
            .filter(|&i| self.entry_matches(i, client_query))
            .collect()
    }

    fn total_hamming_distance(d: &BinaryVector, d_i: &BinaryVector) -> usize {
        (0..NUM_BLOCKS)
            .map(|b| d.get_block(b).hamming_distance(d_i.get_block(b)))
            .sum()
    }
}

fn format_binary_vector(v: &BinaryVector) -> String {
    let bits = v.to_bits();
    let blocks: Vec<String> = bits
        .chunks(BLOCK_SIZE)
        .map(|chunk| {
            chunk
                .iter()
                .map(|&b| if b == 1 { '1' } else { '0' })
                .collect::<String>()
        })
        .collect();
    blocks.join(" ")
}

fn main() {
    println!("TTP Threshold Protocol - Fast Evaluation Version");
    println!("===============================================");
    println!("λ (LAMBDA) = {}", LAMBDA);
    println!("ℓ (BLOCK_SIZE) = {}", BLOCK_SIZE);
    println!("ε (EPSILON) = {}", EPSILON);
    println!("B (NUM_BLOCKS) = {}", NUM_BLOCKS);
    println!("Field Prime p = {}", FIELD_PRIME);
    println!();

    println!("OPTIMIZATION:");
    println!("{}", "=".repeat(80));
    println!("• Removed symbolic polynomial expansion (source of blow-up)");
    println!("• Evaluate threshold polynomial numerically using block distances");
    println!("• Preserves matching semantics: Z=0 iff distance ≥ ε");
    println!();

    let db = Database::random(5);

    println!("DATABASE ENTRIES:");
    println!("{}", "=".repeat(80));
    for (i, entry) in db.entries.iter().enumerate() {
        println!("Entry {}: {}", i, format_binary_vector(entry));
    }
    println!();

    let client_query = BinaryVector::random();

    println!("CLIENT QUERY:");
    println!("{}", "=".repeat(80));
    println!("Query:   {}", format_binary_vector(&client_query));
    println!();

    let mut protocol = TTPProtocol::new(db);
    protocol.build_entry_polynomials();
    println!();

    println!("CLIENT COMPUTATION:");
    println!("{}", "=".repeat(80));
    let res_values = protocol.client_evaluate(&client_query);
    println!("Computed {} results [res_i]_n:", res_values.len());
    for (i, &res) in res_values.iter().enumerate() {
        println!("  res_{} = S_{}(d) = {} (mod {})", i, i, res, FIELD_PRIME);
    }
    println!();

    println!("SERVER VERIFICATION:");
    println!("{}", "=".repeat(80));
    let (has_match, detected_matches) = protocol.server_check(&res_values);

    for (i, &res) in res_values.iter().enumerate() {
        let unmasked = mod_add(res, -protocol.r_blinds[i], FIELD_PRIME);
        println!(
            "Entry {}: res_{} - r_{} = {} {}",
            i,
            i,
            i,
            unmasked,
            if unmasked != 0 { "✓ MATCH" } else { "✗" }
        );
    }
    println!();

    if has_match {
        println!("✓ SERVER RESULT: MATCH EXISTS");
        println!("  Detected matching entries: {:?}", detected_matches);
    } else {
        println!("✗ SERVER RESULT: NO MATCH");
    }
    println!();

    println!("VERIFICATION (Ground Truth):");
    println!("{}", "=".repeat(80));
    let actual_matches = protocol.get_actual_matches(&client_query);

    if !actual_matches.is_empty() {
        println!("Actual matching entries: {:?}", actual_matches);
        for idx in &actual_matches {
            let distance = TTPProtocol::total_hamming_distance(
                &client_query,
                &protocol.database.entries[*idx],
            );
            println!("  Entry {}: total distance = {}", idx, distance);
        }
    } else {
        println!("No actual matches");
    }

    println!();
    let correct = detected_matches == actual_matches;
    println!(
        "Protocol correctness: {}",
        if correct {
            "✓ CORRECT"
        } else {
            "✗ INCORRECT"
        }
    );

    println!();
    println!("DETAILED ANALYSIS:");
    println!("{}", "=".repeat(80));
    for (i, entry) in protocol.database.entries.iter().enumerate() {
        let total_distance = TTPProtocol::total_hamming_distance(&client_query, entry);

        print!("Entry {}: distance = {:3} | Blocks: [", i, total_distance);
        for b in 0..NUM_BLOCKS {
            let block_dist = client_query
                .get_block(b)
                .hamming_distance(entry.get_block(b));
            let is_match = block_dist < EPSILON;
            print!("{:2}{}", block_dist, if is_match { "✓" } else { "✗" });
            if b < NUM_BLOCKS - 1 {
                print!(" ");
            }
        }

        let fully_matches = protocol.entry_matches(i, &client_query);
        println!("] {}", if fully_matches { "✓ FULL MATCH" } else { "" });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_threshold_value_behavior() {
        for d in 0..BLOCK_SIZE {
            let z = TTPProtocol::threshold_value_for_distance(d);
            if d < EPSILON {
                assert_ne!(z, 0, "distance {} should be non-zero", d);
            } else {
                assert_eq!(z, 0, "distance {} should be zero", d);
            }
        }
    }

    #[test]
    fn test_entry_matches() {
        let query_bits = vec![0; LAMBDA];
        let mut entry_bits = vec![0; LAMBDA];

        // Create entry with distance < EPSILON in all blocks
        for block_idx in 0..NUM_BLOCKS {
            for i in 0..(EPSILON - 1) {
                entry_bits[block_idx * BLOCK_SIZE + i] = 1;
            }
        }

        let query = BinaryVector::new(query_bits);
        let entry = BinaryVector::new(entry_bits);

        let db = Database {
            entries: vec![entry],
        };
        let mut protocol = TTPProtocol::new(db);

        protocol.build_entry_polynomials();
        let res_values = protocol.client_evaluate(&query);
        let (has_match, matches) = protocol.server_check(&res_values);

        assert!(has_match);
        assert_eq!(matches, vec![0]);
    }

    #[test]
    fn test_no_match() {
        let query_bits = vec![0; LAMBDA];
        let entry_bits = vec![1; LAMBDA];

        let query = BinaryVector::new(query_bits);
        let entry = BinaryVector::new(entry_bits);

        let db = Database {
            entries: vec![entry],
        };
        let mut protocol = TTPProtocol::new(db);

        protocol.build_entry_polynomials();
        let res_values = protocol.client_evaluate(&query);
        let (has_match, _) = protocol.server_check(&res_values);

        assert!(!has_match);
    }
}
