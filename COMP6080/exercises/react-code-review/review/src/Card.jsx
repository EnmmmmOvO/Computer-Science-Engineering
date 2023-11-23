import React from 'react';
import cardStyles from './Card.module.css';

export default ({ avatar_url, name, url }) => (
    <div className={cardStyles.card}>
        <img
            src={avatar_url}
            alt={name}
            className={cardStyles.cardimg}
        />
        <a href={url}>{name}</a>
    </div>
)
