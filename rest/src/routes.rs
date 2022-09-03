// Copyright (C) 2019-2022 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use super::*;

impl<N: Network, B: 'static + BlockStorage<N>, P: 'static + ProgramStorage<N>> Server<N, B, P> {
    /// Initializes the routes, given the ledger and ledger sender.
    pub fn routes(
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
        ledger_sender: LedgerSender<N>,
    ) -> impl Filter<Extract = impl Reply, Error = Rejection> + Clone {
        // GET /testnet3/latest/height
        let latest_height = warp::get()
            .and(warp::path!("testnet3" / "latest" / "height"))
            .and(with(ledger.clone()))
            .and_then(Self::latest_height);

        // GET /testnet3/latest/hash
        let latest_hash = warp::get()
            .and(warp::path!("testnet3" / "latest" / "hash"))
            .and(with(ledger.clone()))
            .and_then(Self::latest_hash);

        // GET /testnet3/latest/block
        let latest_block = warp::get()
            .and(warp::path!("testnet3" / "latest" / "block"))
            .and(with(ledger.clone()))
            .and_then(Self::latest_block);

        // GET /testnet3/block/{height}
        let get_block = warp::get()
            .and(warp::path!("testnet3" / "block" / u32))
            .and(with(ledger.clone()))
            .and_then(Self::get_block);

        // GET /testnet3/statePath/{commitment}
        let state_path = warp::get()
            .and(warp::path!("testnet3" / "statePath"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(ledger.clone()))
            .and_then(Self::state_path);

        // GET /testnet3/records/all
        let records_all = warp::get()
            .and(warp::path!("testnet3" / "records" / "all"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(ledger.clone()))
            .and_then(Self::records_all);

        // GET /testnet3/records/spent
        let records_spent = warp::get()
            .and(warp::path!("testnet3" / "records" / "spent"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(ledger.clone()))
            .and_then(Self::records_spent);

        // GET /testnet3/records/unspent
        let records_unspent = warp::get()
            .and(warp::path!("testnet3" / "records" / "unspent"))
            .and(warp::body::content_length_limit(128))
            .and(warp::body::json())
            .and(with(ledger.clone()))
            .and_then(Self::records_unspent);

        // GET /testnet3/transactions/{height}
        let get_transactions = warp::get()
            .and(warp::path!("testnet3" / "transactions" / u32))
            .and(with(ledger.clone()))
            .and_then(Self::get_transactions);

        // GET /testnet3/transaction/{id}
        let get_transaction = warp::get()
            .and(warp::path!("testnet3" / "transaction" / ..))
            .and(warp::path::param::<N::TransactionID>())
            .and(warp::path::end())
            .and(with(ledger))
            .and_then(Self::get_transaction);

        // POST /testnet3/transaction/broadcast
        let transaction_broadcast = warp::post()
            .and(warp::path!("testnet3" / "transaction" / "broadcast"))
            .and(warp::body::content_length_limit(10 * 1024 * 1024))
            .and(warp::body::json())
            .and(with(ledger_sender))
            .and_then(Self::transaction_broadcast);

        // Return the list of routes.
        latest_height
            .or(latest_hash)
            .or(latest_block)
            .or(get_block)
            .or(state_path)
            .or(records_all)
            .or(records_spent)
            .or(records_unspent)
            .or(get_transactions)
            .or(get_transaction)
            .or(transaction_broadcast)
    }
}

impl<N: Network, B: 'static + BlockStorage<N>, P: 'static + ProgramStorage<N>> Server<N, B, P> {
    /// Returns the latest block height.
    async fn latest_height(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_height()))
    }

    /// Returns the latest block hash.
    async fn latest_hash(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_hash()))
    }

    /// Returns the latest block.
    async fn latest_block(ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().latest_block().or_reject()?))
    }

    /// Returns the block for the given block height.
    async fn get_block(height: u32, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_block(height).or_reject()?))
    }

    /// Returns the state path for the given commitment.
    async fn state_path(commitment: Field<N>, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().to_state_path(&commitment).or_reject()?))
    }

    /// Returns all of the records for the given view key.
    async fn records_all(view_key: ViewKey<N>, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records: IndexMap<_, _> = ledger.read().find_records(&view_key, RecordsFilter::All).or_reject()?.collect();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the spent records for the given view key.
    async fn records_spent(
        view_key: ViewKey<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records =
            ledger.read().find_records(&view_key, RecordsFilter::Spent).or_reject()?.collect::<IndexMap<_, _>>();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the unspent records for the given view key.
    async fn records_unspent(
        view_key: ViewKey<N>,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        // Fetch the records using the view key.
        let records =
            ledger.read().find_records(&view_key, RecordsFilter::Unspent).or_reject()?.collect::<IndexMap<_, _>>();
        // Return the records.
        Ok(reply::with_status(reply::json(&records), StatusCode::OK))
    }

    /// Returns the transactions for the given block height.
    async fn get_transactions(height: u32, ledger: Arc<RwLock<Ledger<N, B, P>>>) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_transactions(height).or_reject()?))
    }

    /// Returns the transaction for the given transaction ID.
    async fn get_transaction(
        transaction_id: N::TransactionID,
        ledger: Arc<RwLock<Ledger<N, B, P>>>,
    ) -> Result<impl Reply, Rejection> {
        Ok(reply::json(&ledger.read().get_transaction(transaction_id).or_reject()?))
    }

    /// Broadcasts the transaction to the ledger.
    async fn transaction_broadcast(
        transaction: Transaction<N>,
        ledger_sender: LedgerSender<N>,
    ) -> Result<impl Reply, Rejection> {
        // Send the transaction to the ledger.
        match ledger_sender.send(LedgerRequest::TransactionBroadcast(transaction)).await {
            Ok(()) => Ok("OK"),
            Err(error) => Err(reject::custom(RestError::Request(format!("{error}")))),
        }
    }
}