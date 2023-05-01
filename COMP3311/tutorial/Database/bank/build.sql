--
-- Simple bank database
-- Invokes other scripts to build and populate the database
--

-- Remove old instances of database

\i rmdb.sql

-- Create Accounts, Branches, Customers tables

\i schema.sql

-- Add functions+triggers to maintain assets

\i assets.sql

-- Insert tuples

\i populate.sql

