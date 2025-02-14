// @generated automatically by Diesel CLI.

diesel::table! {
    knowledge (id) {
        id -> Integer,
        content -> Text,
        encoding -> Text,
        created_at -> Timestamp,
        updated_at -> Timestamp,
    }
}
